# ZxLean

[![CI](https://github.com/adnathanail/zx-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/adnathanail/zx-lean/actions/workflows/ci.yml)
[![ty](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/astral-sh/ty/main/assets/badge/v0.json)](https://github.com/astral-sh/ty)
[![Ruff](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/astral-sh/ruff/main/assets/badge/v2.json)](https://github.com/astral-sh/ruff)
[![prek](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/j178/prek/master/docs/assets/badge-v0.json)](https://github.com/j178/prek)
[![Python 3.14+](https://img.shields.io/badge/python-3.14+-blue.svg)](https://www.python.org/downloads/)
[![TypeScript](https://img.shields.io/badge/TypeScript-3178C6?logo=typescript&logoColor=fff)](https://www.typescriptlang.org)

## Usage

Install the [Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

## Development

### Tooling

#### Prek

[Install prek](https://github.com/j178/prek) and run
```
prek --install
```

### ZX viewing widget

The InfoView widget lives in `zx_view_widget/src/`

It is a React component, written in Typescript, bundled with rollup

`lake` handles `npm install` and the JS bundle automatically

### PyZX daemon

The widget sends diagram data to a local Flask server for processing

The daemon starts automatically when `ZxLean.Visualize` is imported

Logs are written to `pyzx_daemon/pyzx_daemon.log`
