import SpLean.Algebraic.Phases.RatPhase
import SpLean.Algebraic.Phases.CirclePhase
import SpLean.Algebraic.Phases.NormPhase
import SpLean.ZXDiagram

/-!
# Three candidate phase types, side by side

Open this file and step through it. Everything below either `#eval`s or is
checked at build time, so if a claim is wrong the build says so.

| | `RatPhase` (A) | `CirclePhase` (B) | `NormPhase` (C) |
|---|---|---|---|
| carrier | `ℚ`, opaque | `ℚ ⧸ 2ℤ` | `{q : ℚ // 0 ≤ q < 2}` |
| `=` is phase equality | ✗ (use `equiv`) | ✓ | ✓ |
| lawful `BEq` | ✓ | ✓ | ✓ |
| `AddCommGroup` | inherited, 1 line | inherited, 1 line | hand-proved, ~40 lines |
| `angle : → ℝ` | ✓ and a group hom | **impossible** | ✓ but not a hom |
| `expI : → ℂ` | ✓ | ✓ | ✓ |
| observations cost a proof | no | yes (`Quotient.lift`) | no |
| literals carry proofs | no | no | yes |
| renders phase as written | ✓ | ✗ (always `[0, 2π)`) | ✗ (always `[0, 2π)`) |

The bottom line the files argue for: A is the only one where `angle` is a group
hom, and that is the property the semantics in `SpLean/Algebraic/Semantics.lean`
and every proof in `SemanticsTesting/` is built on.
-/

open SpLean.Phases

/-! ## 0. What we have today, for reference

The current `Phase` has a `BEq` that disagrees with its `DecidableEq`, and an
`add` that never reduces. Both `#eval`s below are the status quo. -/

#eval ((⟨1, 2⟩ : Phase) == ⟨2, 4⟩)             -- true   -- the custom BEq
#eval (decide ((⟨1, 2⟩ : Phase) = ⟨2, 4⟩))     -- false  -- the derived DecidableEq
#eval ((⟨2, 3⟩ : Phase) + ⟨2, 3⟩)              -- {num := 12, den := 9} -- unreduced

/-! ## 1. Display

`RatPhase` shows the phase you wrote. The other two have the branch cut baked
in, so a negative phase comes back as its positive representative. -/

#eval (RatPhase.ofRat (-1 / 4)).format          -- "-π/4"
#eval (CirclePhase.ofRat (-1 / 4)).format       -- "7π/4"
#eval (NormPhase.ofRat (-1 / 4)).format         -- "7π/4"

#eval (RatPhase.ofRat (5 / 2)).format           -- "5π/2"
#eval (CirclePhase.ofRat (5 / 2)).format        -- "π/2"
#eval (NormPhase.ofRat (5 / 2)).format          -- "π/2"

-- All three reduce fractions, unlike the current `Phase.add`:
#eval (RatPhase.ofRat (2 / 3) + RatPhase.ofRat (2 / 3)).format     -- "4π/3"
#eval (CirclePhase.ofRat (2 / 3) + CirclePhase.ofRat (2 / 3))      -- 4π/3
#eval (NormPhase.ofRat (2 / 3) + NormPhase.ofRat (2 / 3))          -- 4π/3

/-! ## 2. Is `2π` equal to `0`?

This is the whole trade. In A it is not — you ask `equiv` instead, and that call
is the *only* place `red` appears in the entire development. In B and C it is
equality on the nose. -/

example : RatPhase.ofRat 2 ≠ 0 := by
  intro h
  have h' : (2 : ℚ) = 0 := congrArg RatPhase.toRat h
  norm_num at h'

example : RatPhase.equiv (RatPhase.ofRat 2) 0 := by
  show RatPhase.ofRat (red 2) = RatPhase.ofRat (red 0)
  rw [red_two, red_zero]

example : CirclePhase.ofRat 2 = 0 := CirclePhase.ofRat_two
example : NormPhase.ofRat 2 = 0 := NormPhase.ofRat_two

/-! ## 3. `angle` — the deciding property

`RatPhase.angle` is a group hom into `ℝ`, so a fusion-shaped lemma is a
`push_cast; ring`. -/

example (p q : RatPhase) : (p + q).angle = p.angle + q.angle := RatPhase.angle_add p q

/-! `CirclePhase.angle` **does not exist**: uncomment to see it fail. `q` and
`q + 2` are the same value but `q·π ≠ (q+2)·π`, so there is nothing to lift.
Only the angle of the canonical representative is definable, and that is not
additive either.

    example (p q : CirclePhase) : (p + q).angle = p.angle + q.angle := ...
-/

#check @CirclePhase.repAngle

/-! `NormPhase.angle` exists, but the hom law is *false* — the constructor has
already wrapped the sum back into `[0, 2π)`. -/
#check @NormPhase.angle_not_additive

/-! ## 4. What all three agree on

`e^{iqπ}` is the only observation blind to the representative, so it is the only
thing that works uniformly. If you pick B or C, this — not `angle` — is what
`zSpiderSem` and `xSpiderSem` have to be reformulated around, and every
`simp only [..., Phase.angle]` in `SemanticsTesting/` becomes a lemma about
exponentials. -/

example (p q : RatPhase)    : (p + q).expI = p.expI * q.expI := RatPhase.expI_add p q
example (p q : CirclePhase) : (p + q).expI = p.expI * q.expI := CirclePhase.expI_add p q
example (p q : NormPhase)   : (p + q).expI = p.expI * q.expI := NormPhase.expI_add p q

/-! ## 5. Reflection

`reflectPhase` in `SpLean/Tactics.lean` has to build an `Expr` for a phase from
a `MetaM` computation.

* A: a numerator and a denominator, as today.
* B: a coercion applied to a `ℚ` literal, and goals display `⟦·⟧`; `decide` and
  `whnf` do not reduce through quotient equality, which is the path
  `applyRewrite` depends on.
* C: a numerator, a denominator, **and two proof terms** — and `by decide` does
  not discharge them (`Rat.blt` gets stuck on an unevaluated `1 / 2`), so the
  certificates have to be built by hand.
-/
