# [<img width="32" height="32" alt="SpLean logo" src="./splean-logo-32@4x.png" />](https://github.com/adnathanail/drawing-with-zx) SpLean

[![CI](https://github.com/adnathanail/splean/actions/workflows/ci.yml/badge.svg)](https://github.com/adnathanail/splean/actions/workflows/ci.yml)
[![prek](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/j178/prek/master/docs/assets/badge-v0.json)](https://github.com/j178/prek)
[![TypeScript](https://img.shields.io/badge/TypeScript-3178C6?logo=typescript&logoColor=fff)](https://www.typescriptlang.org)

## Usage

Install the [Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

At the top of your file:
```lean
import SpLean.All

open SpLean
```

Create a diagram and view it in the InfoView:
```lean
def zCnotZ : ZXDiagram :=
  .ofList [
      .input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨0, 1⟩, .spider .Z ⟨1, 1⟩, .output 0,
      .input 1, .spider .X ⟨0, 1⟩, .output 1
    ]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨2, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩]

#zx zCnotZ
```

### In proofs

To view the current state of a specific proof as a diagram:
```lean
theorem zHadXSimp : zHadX ≈z zHadXSimplified := by
  with_panel_widgets [ZXPanel]
    zx_cc 3
    zx_hh 2 5
    zx_sp 1 3
    zx_id 1
    zx_rfl
```

To have the state shown as a diagram for all proofs in a file, at the top add:
```lean
show_panel_widgets [local ZXPanel]
```

### Other InfoWindow options

To enable the `Selection Panel` (allows you to shift click sub-expressions in the InfoWindow, to view them separately)
```lean
import ProofWidgets.Component.Panel.SelectionPanel
show_panel_widgets [local ZXPanel, local ProofWidgets.SelectionPanel]
```

To enable the `Goal Panel` (displays the main goal of a proof in a separate section in the InfoWindow)
```lean
import ProofWidgets.Component.Panel.GoalTypePanel
show_panel_widgets [local ZXPanel, local ProofWidgets.GoalTypePanel]
```

### Hiding big tactic states

For any reasonably sized diagram, the 'native' display of the tactic state can get quite large, and push the interactive viewer off the screen.
To have this automatically folded up, use the below, and tweak the number to your desired collapse level:

```lean
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 2
```

## Development

### MathLib cache

To prevent building MathLib from scratch:

```sh
lake exe cache get
```

### Prek

[Install prek](https://github.com/j178/prek) and run
```sh
prek --install
```

### ZX viewing widget

The InfoView widget lives in `zx_view_widget/src/`.

It is a React component wrapping the [zxcc](https://github.com/adnathanail/zxcc) web component.

`lake` handles `npm install` and the JS bundle automatically:

```sh
lake build
```
