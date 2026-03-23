import commonjs from '@rollup/plugin-commonjs'
import resolve from '@rollup/plugin-node-resolve'
import replace from '@rollup/plugin-replace'
import terser from '@rollup/plugin-terser'
import { readdirSync, readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import path from 'node:path'

const __dirname = fileURLToPath(new URL('.', import.meta.url))
const pyodideDir = path.join(__dirname, 'node_modules', 'pyodide')

// Bundles pyodide's large binary assets as virtual modules so the widget
// is fully self-contained with no network requests at runtime.
const pyodideBundled = {
  name: 'pyodide-bundled',
  resolveId(id) {
    if (id === 'pyodide-bundled/asm-js') return '\0pyodide-bundled/asm-js'
    if (id === 'pyodide-bundled/wasm') return '\0pyodide-bundled/wasm'
    if (id === 'pyodide-bundled/stdlib') return '\0pyodide-bundled/stdlib'
    if (id === 'pyodide-bundled/lock') return '\0pyodide-bundled/lock'
  },
  load(id) {
    if (id === '\0pyodide-bundled/asm-js') {
      const b64 = readFileSync(path.join(pyodideDir, 'pyodide.asm.js')).toString('base64')
      return `export default "data:text/javascript;base64,${b64}";`
    }
    if (id === '\0pyodide-bundled/wasm') {
      const b64 = readFileSync(path.join(pyodideDir, 'pyodide.asm.wasm')).toString('base64')
      return `export default "data:application/octet-stream;base64,${b64}";`
    }
    if (id === '\0pyodide-bundled/stdlib') {
      const b64 = readFileSync(path.join(pyodideDir, 'python_stdlib.zip')).toString('base64')
      return `export default "data:application/octet-stream;base64,${b64}";`
    }
    if (id === '\0pyodide-bundled/lock') {
      const json = readFileSync(path.join(pyodideDir, 'pyodide-lock.json'), 'utf8')
      return `export default ${json};`
    }
  },
}

// Imports .py files as plain string modules for use with pyodide.runPythonAsync.
// Resolves paths from dist/ back to src/ since tsc compiles there but .py files stay in src/.
const rawPy = {
  name: 'raw-py',
  resolveId(id, importer) {
    if (id.endsWith('.py') && importer) {
      const srcImporter = importer.replace(`${path.sep}dist${path.sep}`, `${path.sep}src${path.sep}`)
      return path.resolve(path.dirname(srcImporter), id)
    }
  },
  load(id) {
    if (id.endsWith('.py')) {
      return `export default ${JSON.stringify(readFileSync(id, 'utf8'))};`
    }
  },
}

const production = process.env.NODE_ENV === 'production'
const outputDir = process.env.OUTPUT_DIR || 'build'

const inputs = readdirSync('dist').filter(f => f.endsWith('.js')).map(f => `dist/${f}`)

export default inputs.map(input => ({
  input,
  output: {
    dir: outputDir,
    format: 'es',
    sourcemap: production ? false : 'inline',
    intro: 'const global = window;',
  },
  external: [
    'react',
    'react-dom',
    'react/jsx-runtime',
    '@leanprover/infoview',
  ],
  plugins: [
    pyodideBundled,
    rawPy,
    resolve({ browser: true }),
    replace({
      preventAssignment: true,
      'typeof window': JSON.stringify('object'),
      'process.env.NODE_ENV': JSON.stringify(production ? 'production' : 'development'),
    }),
    commonjs(),
    production && terser(),
  ],
}))
