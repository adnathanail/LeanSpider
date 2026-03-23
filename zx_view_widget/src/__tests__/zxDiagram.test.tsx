import React from 'react'
import { render, screen, waitFor } from '@testing-library/react'
import { vi, beforeEach, afterEach, test, expect } from 'vitest'

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

function makeFakePyodide(renderResult: unknown = 'abc123') {
  return {
    loadPackage: vi.fn().mockResolvedValue(undefined),
    runPythonAsync: vi.fn().mockResolvedValue(renderResult),
  }
}

// Load a fresh copy of ZXDiagram per test (avoids the pyodideReady singleton
// persisting between tests) and inject a controlled loadPyodide implementation.
async function setup(loadPyodide: () => Promise<unknown>) {
  vi.doMock('pyodide', () => ({ loadPyodide }))
  vi.doMock('pyodide-bundled/asm-js', () => ({ default: 'data:text/javascript;base64,' }))
  vi.doMock('pyodide-bundled/wasm', () => ({ default: 'data:application/octet-stream;base64,' }))
  vi.doMock('pyodide-bundled/stdlib', () => ({ default: 'data:application/octet-stream;base64,' }))
  vi.doMock('pyodide-bundled/lock', () => ({ default: {} }))
  vi.doMock('../zxRender.py', () => ({ default: '' }))
  const { default: ZXDiagram } = await import('../zxDiagram')
  return ZXDiagram
}

beforeEach(() => {
  vi.resetModules()
  // Stub fetch to handle data URL decoding (used to load bundled wasm/stdlib assets).
  vi.stubGlobal('fetch', vi.fn(async (input: string | URL) => {
    if (input.toString().startsWith('data:')) {
      return { arrayBuffer: async () => new ArrayBuffer(0) } as Response
    }
    throw new Error(`Unexpected fetch: ${input}`)
  }))
})

afterEach(() => {
  vi.unstubAllGlobals()
})

test('shows loading state while pyodide initialises', async () => {
  const ZXDiagram = await setup(() => new Promise(() => {})) // never resolves
  render(<ZXDiagram diagram={diagram} />)
  expect(screen.getByText('Rendering...')).toBeInTheDocument()
})

test('renders a PNG image after a successful render', async () => {
  const fakePng = 'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJ'
  const ZXDiagram = await setup(() => Promise.resolve(makeFakePyodide(fakePng)))
  render(<ZXDiagram diagram={diagram} />)
  const img = await waitFor(() => screen.getByRole('img'))
  expect(img).toHaveAttribute('src', `data:image/png;base64,${fakePng}`)
})

test('shows an error message when pyodide fails to load', async () => {
  const ZXDiagram = await setup(() => Promise.reject(new Error('pyodide load failed')))
  render(<ZXDiagram diagram={diagram} />)
  await waitFor(() => screen.getByText(/pyodide load failed/))
})

test('shows an error message when the render call throws', async () => {
  const pyodide = makeFakePyodide()
  // First two runPythonAsync calls are setup (micropip install + zxRenderPy);
  // the third is the render() call which we make fail.
  pyodide.runPythonAsync
    .mockResolvedValueOnce(undefined)
    .mockResolvedValueOnce(undefined)
    .mockRejectedValueOnce(new Error('Python render error'))
  const ZXDiagram = await setup(() => Promise.resolve(pyodide))
  render(<ZXDiagram diagram={diagram} />)
  await waitFor(() => screen.getByText(/Python render error/))
})
