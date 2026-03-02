import * as React from 'react'

const SERVER_URL = 'http://127.0.0.1:5050'

interface ZXWidgetProps {
  diagram: {
    nodes: Array<{
      id: number
      type: 'spider' | 'input' | 'output'
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

export default function ZXDiagram({ diagram }: ZXWidgetProps) {
  const [image, setImage] = React.useState<string | null>(null)
  const [loading, setLoading] = React.useState(false)
  const [error, setError] = React.useState<string | null>(null)
  const [showJson, setShowJson] = React.useState(false)

  const diagramJson = JSON.stringify(diagram, null, 2)

  React.useEffect(() => {
    setLoading(true)
    setError(null)
    setImage(null)
    fetch(`${SERVER_URL}/diagram`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: diagramJson,
    })
      .then((res) => {
        if (!res.ok) throw new Error(`Server returned ${res.status}`)
        return res.json()
      })
      .then((data) => {
        if (data.status === 'ok' && data.image) {
          setImage(data.image)
        } else {
          throw new Error(data.message || 'No image in response')
        }
      })
      .catch((err) => setError(err.message))
      .finally(() => setLoading(false))
  }, [diagramJson])

  return (
    <div style={{ fontFamily: 'monospace', padding: '10px' }}>
      {loading && <p>Rendering diagram...</p>}
      {error && <p style={{ color: 'orange' }}>Server: {error}</p>}
      {image && (
        <div>
          <img
            src={`data:image/png;base64,${image}`}
            alt="ZX Diagram"
            style={{ maxWidth: '100%' }}
          />
        </div>
      )}
      <div style={{ marginTop: '8px' }}>
        <button
          onClick={() => setShowJson(!showJson)}
          style={{ fontSize: '11px', cursor: 'pointer' }}
        >
          {showJson ? 'Hide' : 'Show'} JSON
        </button>
        {showJson && <pre style={{ fontSize: '11px', marginTop: '4px' }}>{diagramJson}</pre>}
      </div>
    </div>
  )
}
