import * as React from 'react'
import { loadPyodide } from 'pyodide'
import pyodideAsmJs from 'pyodide-bundled/asm-js'
import wasmDataUrl from 'pyodide-bundled/wasm'
import stdlibDataUrl from 'pyodide-bundled/stdlib'
import lockFileContents from 'pyodide-bundled/lock'

// Decode a data URL to an ArrayBuffer
async function dataUrlToBuffer(dataUrl: string): Promise<ArrayBuffer> {
  return fetch(dataUrl).then(r => r.arrayBuffer())
}

let pyodideReady: Promise<unknown> | null = null

function loadPyodideLocal() {
  if (pyodideReady) return pyodideReady
  pyodideReady = (async () => {
    // Pre-set _createPyodideModule globally so pyodide skips its dynamic import.
    // pyodideAsmJs is a base64 data URL; decode before eval.
    // CSP allows unsafe-eval in the InfoView webview.
    const asmJsCode = atob(pyodideAsmJs.split(',')[1])
    // eslint-disable-next-line no-eval
    ;(0, eval)(asmJsCode)

    const [wasmBuffer, stdlibBuffer] = await Promise.all([
      dataUrlToBuffer(wasmDataUrl),
      dataUrlToBuffer(stdlibDataUrl),
    ])

    // Patch fetch to serve bundled assets instead of hitting the network.
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

    return loadPyodide({
      indexURL: 'http://pyodide.local/', // fake base URL; assets served via fetch patch above
      lockFileContents: lockFileContents as string,
    })
  })()
  return pyodideReady
}

interface ZXWidgetProps {
  serverUrl: string
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
  const [pythonResult, setPythonResult] = React.useState<string | null>(null)

  React.useEffect(() => {
    loadPyodideLocal().then(async (pyodide: any) => {
      const result = await pyodide.runPythonAsync('1+1')
      setPythonResult(String(result))
    })
  }, [])

  return (
    <div style={{ fontFamily: 'monospace', padding: '10px' }}>
      <p>Python result: {pythonResult ?? 'loading...'}</p>
      <pre style={{ fontSize: '11px' }}>{JSON.stringify(diagram, null, 2)}</pre>
    </div>
  )
}
