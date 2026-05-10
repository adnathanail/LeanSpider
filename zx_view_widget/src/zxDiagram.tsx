import * as d3 from 'd3'
import * as React from 'react'
import { type DiagramData, type RenderData, render as renderDiagram } from './zxRender'
import zxViewerJs from './zxViewer.js'

// Eval the viewer module once and cache the showGraph function.
// pyzx's zx_viewer.inline.js reads `_settings_colors` and `d3` from its scope.
let showGraphFn:
  | ((
      tag: HTMLElement,
      graph: unknown,
      width: number,
      height: number,
      scale: number,
      node_size: number,
      auto_hbox: boolean,
      show_labels: boolean,
      scalar_str: string,
    ) => void)
  | null = null

function getShowGraph(colors: Record<string, string>) {
  if (showGraphFn) return showGraphFn
  const mod: Record<string, unknown> = {}
  // Inject _settings_colors into the function scope
  const fn = new Function(
    'exports',
    '_settings_colors',
    'd3',
    `${zxViewerJs}\nexports.showGraph = showGraph;`,
  )
  fn(mod, colors, d3)
  const show = mod.showGraph as NonNullable<typeof showGraphFn>
  showGraphFn = show
  return show
}

interface ZXWidgetProps {
  diagram: DiagramData
  goal?: DiagramData | null
}

function ZXPanel({ diagram, label }: { diagram: DiagramData; label?: string }) {
  const [retryCount, setRetryCount] = React.useState(0)
  const containerRef = React.useRef<HTMLDivElement>(null)

  // biome-ignore lint/correctness/useExhaustiveDependencies: retryCount is intentionally used to force re-runs on retry
  const { renderData, error } = React.useMemo<{
    renderData: RenderData | null
    error: string | null
  }>(() => {
    try {
      return { renderData: renderDiagram(diagram), error: null }
    } catch (e) {
      return { renderData: null, error: e instanceof Error ? e.message : String(e) }
    }
  }, [diagram, retryCount])

  React.useEffect(() => {
    if (!renderData || !containerRef.current) return
    const container = containerRef.current
    container.innerHTML = ''
    const show = getShowGraph(renderData.colors)
    show(
      container,
      renderData.graph,
      renderData.width,
      renderData.height,
      renderData.scale,
      renderData.node_size,
      renderData.auto_hbox,
      true, // show_labels
      '', // scalar_str
    )
  }, [renderData])

  return (
    <div style={{ flex: '1 1 0', minWidth: 0 }}>
      {label && (
        <div style={{ fontFamily: 'monospace', fontWeight: 'bold', marginBottom: 4 }}>{label}</div>
      )}
      {error ? (
        <div style={{ fontFamily: 'monospace' }}>
          <pre style={{ color: 'red', whiteSpace: 'pre-wrap', wordBreak: 'break-word', margin: 0 }}>
            {error}
          </pre>
          <button type="button" onClick={() => setRetryCount(c => c + 1)}>
            Retry
          </button>
        </div>
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
    } catch {
      /* ignore */
    }
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
    try {
      localStorage.setItem(LAYOUT_KEY, l)
    } catch {
      /* ignore */
    }
  }, [])

  return [layout, setLayout]
}

export default function ZXDiagram({ diagram, goal }: ZXWidgetProps) {
  const [layout, setLayout] = usePersistedLayout()

  if (!goal) {
    return <ZXPanel diagram={diagram} />
  }

  const nextLayout = LAYOUTS[(LAYOUTS.indexOf(layout) + 1) % LAYOUTS.length]
  const buttonLabel = {
    horizontal: '↕ Stack',
    vertical: '⊘ Hide goal',
    goal_hidden: '↔ Side by side',
  }[layout]
  return (
    <div>
      <div style={{ fontFamily: 'monospace', marginBottom: 4 }}>
        <button
          type="button"
          onClick={() => setLayout(nextLayout)}
          style={{ cursor: 'pointer', fontSize: '12px' }}
        >
          {buttonLabel}
        </button>
      </div>
      {layout === 'goal_hidden' ? (
        <ZXPanel diagram={diagram} />
      ) : (
        <div
          style={{
            display: 'flex',
            flexDirection: layout === 'horizontal' ? 'row' : 'column',
            gap: 16,
            alignItems: layout === 'horizontal' ? 'flex-start' : 'stretch',
          }}
        >
          <ZXPanel diagram={diagram} label="Current" />
          <ZXPanel diagram={goal} label="Goal" />
        </div>
      )}
    </div>
  )
}
