import * as React from 'react'

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
  return (
    <pre style={{ fontFamily: 'monospace', padding: '10px' }}>
      {JSON.stringify(diagram, null, 2)}
    </pre>
  )
}
