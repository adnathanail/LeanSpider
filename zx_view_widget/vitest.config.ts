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

const rawPyStub: Plugin = {
  name: 'raw-py-stub',
  transform(code, id) {
    if (id.endsWith('.py')) return `export default ${JSON.stringify(code)};`
  },
}

export default defineConfig({
  plugins: [pyodideBundledStub, rawPyStub],
  test: {
    environment: 'jsdom',
    globals: true,
    include: ['src/**/*.test.{ts,tsx}'],
    setupFiles: ['src/__tests__/setup.ts'],
  },
})
