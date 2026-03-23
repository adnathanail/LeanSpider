declare module 'pyodide-bundled/asm-js' {
  const dataUrl: string
  export default dataUrl
}
declare module 'pyodide-bundled/wasm' {
  const dataUrl: string
  export default dataUrl
}
declare module 'pyodide-bundled/stdlib' {
  const dataUrl: string
  export default dataUrl
}
declare module 'pyodide-bundled/lock' {
  import type { Lockfile } from 'pyodide'
  const contents: Lockfile
  export default contents
}

declare module 'python-deps/load' {
  const deps: string[]
  export default deps
}

declare module 'python-deps/micropip' {
  const deps: string[]
  export default deps
}

declare module '*.py' {
  const code: string
  export default code
}

declare module '*.js' {
  const code: string
  export default code
}
