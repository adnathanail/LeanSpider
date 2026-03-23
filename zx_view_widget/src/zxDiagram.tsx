import * as React from 'react'
import { loadPyodide } from 'pyodide'
import pyodideAsmJs from 'pyodide-bundled/asm-js'
import wasmDataUrl from 'pyodide-bundled/wasm'
import stdlibDataUrl from 'pyodide-bundled/stdlib'
import lockFileContents from 'pyodide-bundled/lock'
import zxRenderPy from './zxRender.py'

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
      lockFileContents: lockFileContents as string,
      packageBaseUrl: 'https://cdn.jsdelivr.net/pyodide/v0.29.3/full/',
    })

    await pyodide.loadPackage(['micropip', 'numpy', 'networkx', 'typing-extensions', 'tqdm', 'matplotlib'])
    await pyodide.runPythonAsync(`
import micropip
await micropip.install(['lark==1.3.1', 'pyperclip==1.11.0', 'pyzx==0.10.0'], deps=False)
`)
    await pyodide.runPythonAsync(zxRenderPy)

    return pyodide
  })()
  return pyodideReady
}

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
  const [png, setPng] = React.useState<string | null>(null)
  const [error, setError] = React.useState<string | null>(null)

  React.useEffect(() => {
    loadPyodideLocal().then(async (pyodide: any) => {
      const b64 = await pyodide.runPythonAsync(
        `render(${JSON.stringify(JSON.stringify(diagram))})`
      )
      setPng(String(b64))
    }).catch(e => setError(String(e)))
  }, [diagram])

  if (error) return <div style={{ color: 'red', fontFamily: 'monospace' }}>{error}</div>
  if (!png) return <div style={{ fontFamily: 'monospace' }}>Rendering...</div>
  return <img src={`data:image/png;base64,${png}`} style={{ maxWidth: '100%' }} />
}
