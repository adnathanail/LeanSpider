import { type DiagramData, ZxDiagramElement } from '@adnathanail/zxcc'
import * as React from 'react'

// Side-effect: touching the class ensures <zx-diagram> is registered even
// if rollup tree-shakes the named export.
void ZxDiagramElement

interface ZXWidgetProps {
  diagram: DiagramData
  goal?: DiagramData | null
}

const LAYOUT_KEY = 'zx-widget-layout'
type Layout = 'horizontal' | 'vertical' | 'goal_hidden'
const LAYOUTS: Layout[] = ['horizontal', 'vertical', 'goal_hidden']

function isLayout(v: unknown): v is Layout {
  return v === 'horizontal' || v === 'vertical' || v === 'goal_hidden'
}

const SHOW_IDS_KEY = 'zx-widget-show-ids'

function usePersistedShowIds(): [boolean, (v: boolean) => void] {
  const [showIds, setShowIdsState] = React.useState<boolean>(() => {
    try {
      return localStorage.getItem(SHOW_IDS_KEY) === 'true'
    } catch {
      return false
    }
  })

  React.useEffect(() => {
    const handler = (e: StorageEvent) => {
      if (e.key === SHOW_IDS_KEY) setShowIdsState(e.newValue === 'true')
    }
    window.addEventListener('storage', handler)
    return () => window.removeEventListener('storage', handler)
  }, [])

  const setShowIds = React.useCallback((v: boolean) => {
    setShowIdsState(v)
    try {
      localStorage.setItem(SHOW_IDS_KEY, String(v))
    } catch {
      /* ignore */
    }
  }, [])

  return [showIds, setShowIds]
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

function ZXPanel({
  diagram,
  label,
  showIds,
}: {
  diagram: DiagramData
  label?: string
  showIds: boolean
}) {
  const ref = React.useRef<ZxDiagramElement | null>(null)
  React.useEffect(() => {
    if (ref.current) {
      // ref.current.viewMode = 'both-vertical'
      ref.current.scale = 30
      ref.current.diagram = diagram
    }
  }, [diagram])
  React.useEffect(() => {
    if (ref.current) ref.current.showLabels = showIds
  }, [showIds])
  return (
    <div style={{ flex: '1 1 0', minWidth: 0 }}>
      {label && (
        <div style={{ fontFamily: 'monospace', fontWeight: 'bold', marginBottom: 4 }}>{label}</div>
      )}
      {React.createElement('zx-diagram', { ref })}
    </div>
  )
}

export default function ZXDiagram({ diagram, goal }: ZXWidgetProps) {
  const [layout, setLayout] = usePersistedLayout()
  const [showIds, setShowIds] = usePersistedShowIds()

  const idsButton = (
    <button
      type="button"
      onClick={() => setShowIds(!showIds)}
      style={{ cursor: 'pointer', fontSize: '12px' }}
    >
      {showIds ? '# Hide IDs' : '# Show IDs'}
    </button>
  )

  if (!goal) {
    return (
      <div>
        <div style={{ fontFamily: 'monospace', marginBottom: 4 }}>{idsButton}</div>
        <ZXPanel diagram={diagram} showIds={showIds} />
      </div>
    )
  }

  const nextLayout = LAYOUTS[(LAYOUTS.indexOf(layout) + 1) % LAYOUTS.length]
  const buttonLabel = {
    horizontal: '↕ Stack',
    vertical: '⊘ Hide RHS',
    goal_hidden: '↔ Side by side',
  }[layout]

  return (
    <div>
      <div style={{ fontFamily: 'monospace', marginBottom: 4, display: 'flex', gap: 8 }}>
        <button
          type="button"
          onClick={() => setLayout(nextLayout)}
          style={{ cursor: 'pointer', fontSize: '12px' }}
        >
          {buttonLabel}
        </button>
        {idsButton}
      </div>
      {layout === 'goal_hidden' ? (
        <ZXPanel diagram={diagram} showIds={showIds} />
      ) : (
        <div
          style={{
            display: 'flex',
            flexDirection: layout === 'horizontal' ? 'row' : 'column',
            gap: 16,
            alignItems: layout === 'horizontal' ? 'flex-start' : 'stretch',
          }}
        >
          <ZXPanel diagram={diagram} label="LHS" showIds={showIds} />
          <ZXPanel diagram={goal} label="RHS" showIds={showIds} />
        </div>
      )}
    </div>
  )
}
