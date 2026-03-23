# LeanZX

[![CI](https://github.com/adnathanail/zx-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/adnathanail/zx-lean/actions/workflows/ci.yml)
[![ty](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/astral-sh/ty/main/assets/badge/v0.json)](https://github.com/astral-sh/ty)
[![Ruff](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/astral-sh/ruff/main/assets/badge/v2.json)](https://github.com/astral-sh/ruff)
[![prek](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/j178/prek/master/docs/assets/badge-v0.json)](https://github.com/j178/prek)
[![TypeScript](https://img.shields.io/badge/TypeScript-3178C6?logo=typescript&logoColor=fff)](https://www.typescriptlang.org)

## Usage

Install the [Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

Create a diagram and view it in the InfoView:
```lean
def zCnotZ : ZXDiagram :=
  .ofList [
      .input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨0, 1⟩, .spider .Z ⟨1, 1⟩, .output 0,
      .input 1, .spider .X ⟨0, 1⟩, .output 1
    ]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨2, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩]

#html zCnotZ.toHtml
```

On first use, the widget downloads pyzx and its dependencies (numpy, networkx, matplotlib) from the internet and caches them. Subsequent renders are fully offline.

## Development

### Tooling

#### Prek

[Install prek](https://github.com/j178/prek) and run
```
prek --install
```

### ZX viewing widget

The InfoView widget lives in `zx_view_widget/src/`.

It is a React component written in TypeScript, bundled with rollup. It runs pyzx directly inside the InfoView using Pyodide (CPython compiled to WebAssembly) — no external processes or servers are required.

The pyodide runtime (~16MB) is bundled into the widget JS at build time so it works without any network access. Python packages (pyzx, numpy, etc.) are fetched from the internet on first use and cached by the browser.

`lake` handles `npm install` and the JS bundle automatically:

```sh
lake build
```
