import SpLean.Hypergraph.Iso
import Mathlib.Data.List.GetD

/-!
# Checking an isomorphism

`Iso`'s conditions are stated with `Hyp.Rel`, which is `Relation.EqvGen` — a
`Prop`, and nothing `decide` can touch. This file gives a computable stand-in
so that, for a *concrete* pair of hypergraphs, an isomorphism can be supplied
as a certificate whose side conditions are discharged by `decide`.

## Soundness only

`Hyp.rep` is one pass of quick-find over the recorded identifications: for each
pair in turn, every wire currently pointing at the first one is repointed at
the second. What is proved about it is `Hyp.rel_rep : H.Rel u (H.rep u)`, and
hence `rep u = rep v → H.Rel u v`.

The converse is deliberately not proved. It is true — one pass of quick-find
does compute the full closure, because each merge relabels an entire class —
but nothing needs it: a certificate is *accepted* when the `rep`s agree, so
only this direction can make `Iso.ofRepEq` unsound. If the check is ever too
weak in practice, that is a completeness bug to fix then, not a soundness one.
-/

namespace SpLean.Hypergraph

variable {Φ : Type} {n m : ℕ}

/-- The representative table: fold over the identifications, each step
repointing every wire that currently shares a representative with the pair's
left end at the representative of its right end.

Threading the table through a `foldl` — rather than recursing on a function
`Fin wires → Fin wires` — is what keeps this affordable. The recursive form
needs the previous level at three places (the test and both branches), so
evaluating it costs `3 ^ idCount`; that is invisible on a diagram with three
identifications and hangs the kernel on one with twenty. -/
def Hyp.repList (H : Hyp Φ n m) : List (Fin H.wires) :=
  (List.finRange H.idCount).foldl
    (fun t k =>
      let a := t.getD (H.ids k).1.val (H.ids k).1
      let b := t.getD (H.ids k).2.val (H.ids k).2
      t.map fun r => if r = a then b else r)
    (List.finRange H.wires)

/-- A representative for each wire, respecting the identifications. -/
def Hyp.rep (H : Hyp Φ n m) (x : Fin H.wires) : Fin H.wires := H.repList.getD x.val x

/-- The table stays as long as there are wires, and every entry is related to
its own index. Both halves are needed together: the length is what lets a
lookup commute with the `List.map` each step performs. -/
theorem Hyp.repList_spec (H : Hyp Φ n m) :
    H.repList.length = H.wires ∧ ∀ x : Fin H.wires, H.Rel x (H.repList.getD x.val x) := by
  unfold Hyp.repList
  refine List.foldlRecOn
    (motive := fun t : List (Fin H.wires) =>
      t.length = H.wires ∧ ∀ x : Fin H.wires, H.Rel x (t.getD x.val x))
    _ _ ?_ ?_
  · refine ⟨by simp, fun x => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp [x.isLt])]
    simp only [List.getElem_finRange]
    rfl
  · rintro t ⟨hlen, ih⟩ k -
    refine ⟨by simpa using hlen, fun x => ?_⟩
    have hx : x.val < t.length := by rw [hlen]; exact x.isLt
    rw [List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_map,
      ← List.getD_eq_getElem _ _ hx]
    by_cases h : t.getD x.val x = t.getD (H.ids k).1.val (H.ids k).1
    · rw [if_pos h]
      exact ((ih x).trans (h ▸ (ih (H.ids k).1).symm)).trans
        ((H.rel_ids k).trans (ih (H.ids k).2))
    · rw [if_neg h]
      exact ih x

theorem Hyp.rel_rep (H : Hyp Φ n m) (u : Fin H.wires) : H.Rel u (H.rep u) :=
  H.repList_spec.2 u

/-- The check that stands in for `Hyp.Rel`. -/
theorem Hyp.rel_of_rep_eq (H : Hyp Φ n m) {u v : Fin H.wires} (h : H.rep u = H.rep v) :
    H.Rel u v :=
  (H.rel_rep u).trans (h ▸ (H.rel_rep v).symm)

/-- Build an `Iso` from data plus conditions that are all decidable, so each
can be discharged by `decide` for concrete hypergraphs.

Every `Hyp.Rel` in `Iso` becomes an equality of representatives. The two
`map_rel` fields are the interesting ones: it is enough to check that each
*recorded identification* is sent to a related pair, since `Rel` is generated
by those — the general statement then follows by induction on the derivation. -/
def Iso.ofRepEq {H₁ H₂ : Hyp Φ n m}
    (wire : Fin H₁.wires → Fin H₂.wires) (wireInv : Fin H₂.wires → Fin H₁.wires)
    (boxPerm : Fin H₁.boxCount ≃ Fin H₂.boxCount)
    (legPerm : ∀ i, Fin (H₁.boxes i).arity ≃ Fin (H₂.boxes (boxPerm i)).arity)
    (hleft : ∀ v, H₁.rep (wireInv (wire v)) = H₁.rep v)
    (hright : ∀ v, H₂.rep (wire (wireInv v)) = H₂.rep v)
    (hids₁ : ∀ k, H₂.rep (wire (H₁.ids k).1) = H₂.rep (wire (H₁.ids k).2))
    (hids₂ : ∀ k, H₁.rep (wireInv (H₂.ids k).1) = H₁.rep (wireInv (H₂.ids k).2))
    (hin : ∀ i, H₂.rep (wire (H₁.inputs i)) = H₂.rep (H₂.inputs i))
    (hout : ∀ j, H₂.rep (wire (H₁.outputs j)) = H₂.rep (H₂.outputs j))
    (hlabel : ∀ i, (H₁.boxes i).label = (H₂.boxes (boxPerm i)).label)
    (hlegs : ∀ i k, H₂.rep (wire ((H₁.boxes i).legs k))
      = H₂.rep ((H₂.boxes (boxPerm i)).legs (legPerm i k))) :
    Iso H₁ H₂ where
  wire := wire
  wireInv := wireInv
  left_inv v := H₁.rel_of_rep_eq (hleft v)
  right_inv v := H₂.rel_of_rep_eq (hright v)
  map_rel u v h := by
    induction h with
    | rel x y hxy =>
        obtain ⟨k, hk⟩ := hxy
        have := hids₁ k
        rw [hk] at this
        exact H₂.rel_of_rep_eq this
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  map_rel_inv u v h := by
    induction h with
    | rel x y hxy =>
        obtain ⟨k, hk⟩ := hxy
        have := hids₂ k
        rw [hk] at this
        exact H₁.rel_of_rep_eq this
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  map_inputs i := H₂.rel_of_rep_eq (hin i)
  map_outputs j := H₂.rel_of_rep_eq (hout j)
  boxPerm := boxPerm
  map_label := hlabel
  legPerm := legPerm
  map_legs i k := H₂.rel_of_rep_eq (hlegs i k)

/-! ## Certificates as plain number tables

`Iso.ofRepEq` wants a `legPerm : ∀ i, Fin (H₁.boxes i).arity ≃ Fin (H₂.boxes _).arity`,
whose type depends on `i`. That is fine to write by hand — a `match` on the
box index, with each branch at a concrete arity — but a tactic cannot easily
*emit* one, which is what stands between this and an automatic
`zx_iso`.

So the whole certificate is restated as untyped `ℕ` tables, with the bounds and
inverse laws as separate hypotheses quantified over `i` up front. Each is a
closed statement about concrete hypergraphs, so each is `by decide`; and
because they are proved once, outside the lambda, they can be applied at `i`
*inside* it. That is what makes the dependent `legPerm` constructible from flat
data. -/

/-- A `Fin`-to-`Fin` function from a table of numbers. -/
def tableFun {a b : ℕ} (f : ℕ → ℕ) (hf : ∀ i : Fin a, f i.val < b) : Fin a → Fin b :=
  fun i => ⟨f i.val, hf i⟩

/-- An `Equiv` between two `Fin`s from a pair of tables that are mutually
inverse where it matters. -/
def finEquivOfTable {a b : ℕ} (f g : ℕ → ℕ)
    (hf : ∀ i : Fin a, f i.val < b) (hg : ∀ j : Fin b, g j.val < a)
    (h₁ : ∀ i : Fin a, g (f i.val) = i.val)
    (h₂ : ∀ j : Fin b, f (g j.val) = j.val) : Fin a ≃ Fin b where
  toFun := tableFun f hf
  invFun := tableFun g hg
  left_inv i := Fin.ext (by simpa [tableFun] using h₁ i)
  right_inv j := Fin.ext (by simpa [tableFun] using h₂ j)

/-- `Iso.ofRepEq` with every piece of data given as a number table. This is the
form a tactic can emit: the tables are list lookups, and every hypothesis is a
closed decidable statement. -/
def Iso.ofTables {H₁ H₂ : Hyp Φ n m}
    (w wInv : ℕ → ℕ) (bp bpInv : ℕ → ℕ) (lp lpInv : ℕ → ℕ → ℕ)
    (hw : ∀ v : Fin H₁.wires, w v.val < H₂.wires)
    (hwInv : ∀ v : Fin H₂.wires, wInv v.val < H₁.wires)
    (hbp : ∀ i : Fin H₁.boxCount, bp i.val < H₂.boxCount)
    (hbpInv : ∀ i : Fin H₂.boxCount, bpInv i.val < H₁.boxCount)
    (hbp₁ : ∀ i : Fin H₁.boxCount, bpInv (bp i.val) = i.val)
    (hbp₂ : ∀ i : Fin H₂.boxCount, bp (bpInv i.val) = i.val)
    (hlp : ∀ (i : Fin H₁.boxCount) (k : Fin (H₁.boxes i).arity),
      lp i.val k.val < (H₂.boxes (tableFun bp hbp i)).arity)
    (hlpInv : ∀ (i : Fin H₁.boxCount) (k : Fin (H₂.boxes (tableFun bp hbp i)).arity),
      lpInv i.val k.val < (H₁.boxes i).arity)
    (hlp₁ : ∀ (i : Fin H₁.boxCount) (k : Fin (H₁.boxes i).arity),
      lpInv i.val (lp i.val k.val) = k.val)
    (hlp₂ : ∀ (i : Fin H₁.boxCount) (k : Fin (H₂.boxes (tableFun bp hbp i)).arity),
      lp i.val (lpInv i.val k.val) = k.val)
    (hleft : ∀ v, H₁.rep (tableFun wInv hwInv (tableFun w hw v)) = H₁.rep v)
    (hright : ∀ v, H₂.rep (tableFun w hw (tableFun wInv hwInv v)) = H₂.rep v)
    (hids₁ : ∀ k, H₂.rep (tableFun w hw (H₁.ids k).1) = H₂.rep (tableFun w hw (H₁.ids k).2))
    (hids₂ : ∀ k, H₁.rep (tableFun wInv hwInv (H₂.ids k).1)
      = H₁.rep (tableFun wInv hwInv (H₂.ids k).2))
    (hin : ∀ i, H₂.rep (tableFun w hw (H₁.inputs i)) = H₂.rep (H₂.inputs i))
    (hout : ∀ j, H₂.rep (tableFun w hw (H₁.outputs j)) = H₂.rep (H₂.outputs j))
    (hlabel : ∀ i, (H₁.boxes i).label = (H₂.boxes (tableFun bp hbp i)).label)
    (hlegs : ∀ (i : Fin H₁.boxCount) (k : Fin (H₁.boxes i).arity),
      H₂.rep (tableFun w hw ((H₁.boxes i).legs k))
        = H₂.rep ((H₂.boxes (tableFun bp hbp i)).legs
            (finEquivOfTable (lp i.val) (lpInv i.val) (hlp i) (hlpInv i) (hlp₁ i) (hlp₂ i) k))) :
    Iso H₁ H₂ :=
  Iso.ofRepEq (tableFun w hw) (tableFun wInv hwInv)
    (finEquivOfTable bp bpInv hbp hbpInv hbp₁ hbp₂)
    (fun i => finEquivOfTable (lp i.val) (lpInv i.val) (hlp i) (hlpInv i) (hlp₁ i) (hlp₂ i))
    hleft hright hids₁ hids₂ hin hout hlabel hlegs

end SpLean.Hypergraph
