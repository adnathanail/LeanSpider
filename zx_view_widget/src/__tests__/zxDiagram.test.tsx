import { render, waitFor } from '@testing-library/react'
import ZXDiagram from '../zxDiagram'

const diagram = {
  nodes: [
    { id: 0, type: 'input' as const, ioId: 0 },
    { id: 1, type: 'spider' as const, color: 'Z' as const, phase: '1/2' },
    { id: 2, type: 'output' as const, ioId: 0 },
  ],
  edges: [
    { src: 0, tgt: 1 },
    { src: 1, tgt: 2 },
  ],
}

afterEach(() => {
  vi.restoreAllMocks()
})

test('sends correct fetch request to daemon', async () => {
  const fetchSpy = vi.spyOn(globalThis, 'fetch').mockResolvedValue(
    new Response(JSON.stringify({ status: 'ok', image: 'dGVzdA==' }), {
      status: 200,
      headers: { 'Content-Type': 'application/json' },
    }),
  )

  render(<ZXDiagram diagram={diagram} />)

  await waitFor(() => expect(fetchSpy).toHaveBeenCalledOnce())
})
