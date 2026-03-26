import * as React from 'react'
import { loadPyodide, version as pyodideVersion } from 'pyodide'
import pyodideAsmJs from 'pyodide-bundled/asm-js'
import wasmDataUrl from 'pyodide-bundled/wasm'
import stdlibDataUrl from 'pyodide-bundled/stdlib'
import lockFileContents from 'pyodide-bundled/lock'
import zxRenderPy from './zxRender.py'
import * as d3 from 'd3'
import zxViewerJs from './zxViewer.js'
import pyodideLoadDeps from 'python-deps/load'
import micropipDeps from 'python-deps/micropip'

async function dataUrlToBuffer(dataUrl: string): Promise<ArrayBuffer> {
  return fetch(dataUrl).then(r => r.arrayBuffer())
}

let pyodideReady: Promise<unknown> | null = null

function loadPyodideLocal() {
  if (pyodideReady) return pyodideReady
  pyodideReady = (async () => {
    const asmJsCode = atob(pyodideAsmJs.split(',')[1])
    // eslint-disable-next-line no-eval
    ;(0, eval)(asmJsCode)

    const [wasmBuffer, stdlibBuffer] = await Promise.all([
      dataUrlToBuffer(wasmDataUrl),
      dataUrlToBuffer(stdlibDataUrl),
    ])

    const realFetch = globalThis.fetch
    globalThis.fetch = async (input: RequestInfo | URL, init?: RequestInit) => {
      const url = input instanceof Request ? input.url : input.toString()
      if (url.endsWith('pyodide.asm.wasm')) {
        return new Response(wasmBuffer, {
          status: 200,
          headers: { 'Content-Type': 'application/wasm' },
        })
      }
      if (url.endsWith('python_stdlib.zip')) {
        return new Response(stdlibBuffer, { status: 200 })
      }
      return realFetch(input, init)
    }

    const pyodide = await loadPyodide({
      indexURL: 'http://pyodide.local/',
      lockFileContents: lockFileContents,
      packageBaseUrl: `https://cdn.jsdelivr.net/pyodide/v${pyodideVersion}/full/`,
    })
    globalThis.fetch = realFetch

    await pyodide.loadPackage(['micropip', ...pyodideLoadDeps])
    // We disable dependency resolution, because some dependencies don't work
    //   with pyodide (e.g. numba), but it turns out we don't actually need them
    await pyodide.runPythonAsync(`
import micropip
await micropip.install(${JSON.stringify(micropipDeps)}, deps=False)
`)
    await pyodide.runPythonAsync(zxRenderPy)

    return pyodide
  })().catch(e => {
    pyodideReady = null
    throw e
  })
  return pyodideReady
}

// Eval the viewer module once and cache the showGraph function.
// pyzx's zx_viewer.inline.js reads `_settings_colors` and `d3` from its scope.
let showGraphFn: ((
  tag: HTMLElement,
  graph: unknown,
  width: number,
  height: number,
  scale: number,
  node_size: number,
  auto_hbox: boolean,
  show_labels: boolean,
  scalar_str: string,
) => void) | null = null

function getShowGraph(colors: Record<string, string>) {
  if (showGraphFn) return showGraphFn
  const mod: Record<string, unknown> = {}
  // Inject _settings_colors into the function scope
  const fn = new Function('exports', '_settings_colors', 'd3', zxViewerJs + '\nexports.showGraph = showGraph;')
  fn(mod, colors, d3)
  showGraphFn = mod.showGraph as typeof showGraphFn
  return showGraphFn!
}

interface DiagramData {
  nodes: Array<{
    id: number
    type: 'spider' | 'input' | 'output' | 'hadamard'
    color?: 'Z' | 'X'
    phase?: string
    ioId?: number
  }>
  edges: Array<{
    src: number
    tgt: number
  }>
}

interface ZXWidgetProps {
  diagram: DiagramData
  goal?: DiagramData | null
}

interface RenderData {
  graph: unknown
  width: number
  height: number
  scale: number
  node_size: number
  colors: Record<string, string>
}

function ZXPanel({ diagram, label }: { diagram: DiagramData; label?: string }) {
  const [renderData, setRenderData] = React.useState<RenderData | null>(null)
  const [error, setError] = React.useState<string | null>(null)
  const [status, setStatus] = React.useState<'loading' | 'rendering'>('loading')
  const [retryCount, setRetryCount] = React.useState(0)
  const containerRef = React.useRef<HTMLDivElement>(null)

  // Step 1: Load Pyodide + D3, compute graph JSON via Python
  // biome-ignore lint/correctness/useExhaustiveDependencies: retryCount is intentionally used to force re-runs on retry
  React.useEffect(() => {
    setError(null)
    setRenderData(null)
    setStatus('loading')

    loadPyodideLocal().then(async (pyodide) => {
      setStatus('rendering')
      const resultStr = await (pyodide as { runPythonAsync(code: string): Promise<unknown> }).runPythonAsync(
        `render(${JSON.stringify(JSON.stringify(diagram))})`
      )
      const data = JSON.parse(String(resultStr)) as RenderData
      setRenderData(data)
    }).catch(e => {
      const msg = (e instanceof Error && 'type' in e) ? e.message : String(e)
      setError(msg)
    })
  }, [diagram, retryCount])

  // Step 2: Once we have graph data and the container is mounted, render D3 SVG
  React.useEffect(() => {
    if (!renderData || !containerRef.current) return
    const container = containerRef.current
    // Clear previous SVG
    container.innerHTML = ''
    const show = getShowGraph(renderData.colors)
    show(
      container,
      renderData.graph,
      renderData.width,
      renderData.height,
      renderData.scale,
      renderData.node_size,
      true, // auto_hbox
      true, // show_labels
      '',   // scalar_str
    )
  }, [renderData])

  return (
    <div style={{ flex: '1 1 0', minWidth: 0 }}>
      {label && <div style={{ fontFamily: 'monospace', fontWeight: 'bold', marginBottom: 4 }}>{label}</div>}
      {error ? (
        <div style={{ fontFamily: 'monospace' }}>
          <pre style={{ color: 'red', whiteSpace: 'pre-wrap', wordBreak: 'break-word', margin: 0 }}>{error}</pre>
          <button type="button" onClick={() => setRetryCount(c => c + 1)}>Retry</button>
        </div>
      ) : !renderData ? (
        <div style={{ fontFamily: 'monospace' }}>{status === 'loading' ? 'Loading Python environment...' : 'Rendering...'}</div>
      ) : (
        <div ref={containerRef} style={{ overflow: 'auto', backgroundColor: 'white' }} />
      )}
    </div>
  )
}

const LAYOUT_KEY = 'zx-widget-layout'
type Layout = 'horizontal' | 'vertical' | 'goal_hidden'
const LAYOUTS: Layout[] = ['horizontal', 'vertical', 'goal_hidden']

function isLayout(v: unknown): v is Layout {
  return v === 'horizontal' || v === 'vertical' || v === 'goal_hidden'
}

function usePersistedLayout(): [Layout, (l: Layout) => void] {
  const [layout, setLayoutState] = React.useState<Layout>(() => {
    try {
      const stored = localStorage.getItem(LAYOUT_KEY)
      if (isLayout(stored)) return stored
    } catch { /* ignore */ }
    return 'horizontal'
  })

  // Listen for changes from other widget instances
  React.useEffect(() => {
    const handler = (e: StorageEvent) => {
      if (e.key === LAYOUT_KEY && isLayout(e.newValue)) {
        setLayoutState(e.newValue)
      }
    }
    window.addEventListener('storage', handler)
    return () => window.removeEventListener('storage', handler)
  }, [])

  const setLayout = React.useCallback((l: Layout) => {
    setLayoutState(l)
    try { localStorage.setItem(LAYOUT_KEY, l) } catch { /* ignore */ }
  }, [])

  return [layout, setLayout]
}

export default function ZXDiagram({ diagram, goal }: ZXWidgetProps) {
  const [layout, setLayout] = usePersistedLayout()

  if (!goal) {
    return <ZXPanel diagram={diagram} />
  }

  const nextLayout = LAYOUTS[(LAYOUTS.indexOf(layout) + 1) % LAYOUTS.length]
  const buttonLabel = { horizontal: '↕ Stack', vertical: '⊘ Hide goal', goal_hidden: '↔ Side by side' }[layout]
  return (
    <div>
      <div style={{ fontFamily: 'monospace', marginBottom: 4 }}>
        <button
          type="button"
          onClick={() => setLayout(nextLayout)}
          style={{ cursor: 'pointer', fontSize: '12px' }}
        >{buttonLabel}</button>
      </div>
      {layout === 'goal_hidden' ? (
        <ZXPanel diagram={diagram} />
      ) : (
        <div style={{
          display: 'flex',
          flexDirection: layout === 'horizontal' ? 'row' : 'column',
          gap: 16,
          alignItems: layout === 'horizontal' ? 'flex-start' : 'stretch',
        }}>
          <ZXPanel diagram={diagram} label="Current" />
          <ZXPanel diagram={goal} label="Goal" />
        </div>
      )}
    </div>
  )
}
