import commonjs from '@rollup/plugin-commonjs'
import resolve from '@rollup/plugin-node-resolve'
import replace from '@rollup/plugin-replace'
import terser from '@rollup/plugin-terser'
import { readdirSync } from 'fs'

const production = process.env.NODE_ENV === 'production'

const inputs = readdirSync('dist').filter(f => f.endsWith('.js')).map(f => `dist/${f}`)

export default inputs.map(input => ({
  input,
  output: {
    dir: 'build',
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
