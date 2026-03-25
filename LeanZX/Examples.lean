import LeanZX.ZXDiagram

-- Z CNOT Z
def zCnotZ : ZXDiagram :=
  .ofList [
      .input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨0, 1⟩, .spider .Z ⟨1, 1⟩, .output 0,
      .input 1, .spider .X ⟨0, 1⟩, .output 1
    ]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨2, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩]
def cnot : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0, .input 1, .spider .X ⟨0, 1⟩, .output 1]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 4⟩, ⟨3, 4⟩, ⟨4, 5⟩]
