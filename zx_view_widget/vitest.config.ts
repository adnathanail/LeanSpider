import { defineConfig } from 'vitest/config'
import type { Plugin } from 'vite'

// Lightweight stubs for the pyodide-bundled virtual modules and .py imports.
// The real implementations (which embed megabytes of binary data) live in
// rollup.config.js and are only needed for production builds.
const pyodideBundledStub: Plugin = {
  name: 'pyodide-bundled-stub',
  resolveId(id) {
    if (id.startsWith('pyodide-bundled/')) return `\0${id}`
  },
  load(id) {
    if (id.startsWith('\0pyodide-bundled/')) {
      return `export default "data:application/octet-stream;base64,";`
    }
  },
}

const pythonDepsStub: Plugin = {
  name: 'python-deps-stub',
  resolveId(id) {
    if (id === 'python-deps/load' || id === 'python-deps/micropip') return `\0${id}`
  },
  load(id) {
    if (id === '\0python-deps/load' || id === '\0python-deps/micropip') {
      return `export default [];`
    }
  },
}

const rawPyStub: Plugin = {
  name: 'raw-py-stub',
  transform(code, id) {
    if (id.endsWith('.py')) return `export default ${JSON.stringify(code)};`
  },
}

export default defineConfig({
  plugins: [pyodideBundledStub, pythonDepsStub, rawPyStub],
  test: {
    environment: 'jsdom',
    globals: true,
    include: ['src/**/*.test.{ts,tsx}'],
    setupFiles: ['src/__tests__/setup.ts'],
  },
})
