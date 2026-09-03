import { readdirSync } from 'node:fs'
import commonjs from '@rollup/plugin-commonjs'
import resolve from '@rollup/plugin-node-resolve'
import replace from '@rollup/plugin-replace'
import terser from '@rollup/plugin-terser'

const production = process.env.NODE_ENV === 'production'
const outputDir = process.env.OUTPUT_DIR || 'build'

// One bundle per top-level module: those are the widget entry points. Shared
// code lives in subdirectories (`dist/lib/`) so it is bundled into its
// importers rather than emitted as a widget of its own.
const inputs = readdirSync('dist')
  .filter(f => f.endsWith('.js'))
  .map(f => `dist/${f}`)

export default inputs.map(input => ({
  input,
  output: {
    dir: outputDir,
    format: 'es',
    sourcemap: production ? false : 'inline',
    intro: 'const global = window;',
  },
  external: ['react', 'react-dom', 'react/jsx-runtime', '@leanprover/infoview'],
  plugins: [
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
