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

// Make d3 available on window for the viewer JS
;(window as unknown as Record<string, unknown>).d3 = d3

// Eval the viewer module once and cache the showGraph function
let showGraphFn: ((
  container: HTMLElement,
  graph: unknown,
  width: number,
  height: number,
  scale: number,
  node_size: number,
  colors: Record<string, string>,
  show_labels: boolean,
) => void) | null = null

function getShowGraph() {
  if (showGraphFn) return showGraphFn
  // The viewer JS exports showGraph — eval it as a module
  const mod: Record<string, unknown> = {}
  const fn = new Function('exports', zxViewerJs + '\nexports.showGraph = showGraph;')
  fn(mod)
  showGraphFn = mod.showGraph as typeof showGraphFn
  return showGraphFn!
}

interface ZXWidgetProps {
  diagram: {
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
}

interface RenderData {
  graph: unknown
  width: number
  height: number
  scale: number
  node_size: number
  colors: Record<string, string>
}

export default function ZXDiagram({ diagram }: ZXWidgetProps) {
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
    const show = getShowGraph()
    show(
      container,
      renderData.graph,
      renderData.width,
      renderData.height,
      renderData.scale,
      renderData.node_size,
      renderData.colors,
      true, // show_labels
    )
  }, [renderData])

  if (error) return (
    <div style={{ fontFamily: 'monospace' }}>
      <pre style={{ color: 'red', whiteSpace: 'pre-wrap', wordBreak: 'break-word', margin: 0 }}>{error}</pre>
      <button type="button" onClick={() => setRetryCount(c => c + 1)}>Retry</button>
    </div>
  )
  if (!renderData) return <div style={{ fontFamily: 'monospace' }}>{status === 'loading' ? 'Loading Python environment...' : 'Rendering...'}</div>
  return <div ref={containerRef} style={{ overflow: 'auto', backgroundColor: 'white' }} />
}
