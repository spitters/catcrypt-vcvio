/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptVCVio.Rust.HaxWP

/-!
# Tests of the transfer of hax-lean triples to `RustOracleComp`

`incrIndex` reads `a[x + 1]` with a checked 64-bit increment, the two guarded operations
`Hax.addM_w 64` and `Hax.indexM`. Its hax-lean triple is proved by `rust_vc`; the tests derive
its panic freedom and transfer the triple and the panic freedom to `RustOracleComp unifSpec`.
-/

set_option autoImplicit false

namespace HaxWPTest

open CatCrypt.VCVio.Rust Hax _root_.Std.WP Lean.Order
open scoped OracleComp.Necessary

/-- `a[x + 1]` with a checked 64-bit increment. -/
def incrIndex (p : Array Int × Int) : RustM Int := do
  let j ← addM_w 64 p.2 1
  indexM p.1 j

/-- The precondition of `incrIndex`. -/
def IncrIndexPre (p : Array Int × Int) : Prop :=
  0 ≤ p.2 ∧ p.2 + 1 < p.1.size ∧ p.2 + 1 < 2 ^ 64

/-- The hax-lean triple of `incrIndex`: under `IncrIndexPre`, it returns a value. -/
theorem incrIndex_triple (p : Array Int × Int) :
    ⦃ IncrIndexPre p ⦄ incrIndex p ⦃ fun _ => True ⦄ := by
  unfold incrIndex IncrIndexPre
  rust_vc

/-- `incrIndex` is panic-free on `IncrIndexPre`. -/
theorem incrIndex_panicFreeOn : UCMonad.RustMBridge.PanicFreeOn IncrIndexPre incrIndex := by
  intro p hp
  have hw := (incrIndex_triple p).le_wp hp
  cases h : incrIndex p with
  | ok v => exact ⟨v, rfl⟩
  | fail e =>
    rw [h] at hw
    change (Lean.Order.bot : Aeneas.Std.Error → Prop) e at hw
    simp_all
  | div => rw [h] at hw; exact hw.elim

example (p : Array Int × Int) :
    Triple (liftRustM (incrIndex p) : RustOracleComp unifSpec Int) (IncrIndexPre p)
      (fun _ => True)
      ((fun _ => False, fun _ => False, EStackEnd.mk) :
        EStack⟨CatCrypt.VCVio.Rust.Error → Prop, Unit → Prop⟩) :=
  triple_liftRustM_of_panicFreeOn incrIndex_panicFreeOn p

example (p : Array Int × Int) (hp : IncrIndexPre p) : ∃ v,
    (liftRustM (incrIndex p) : RustOracleComp unifSpec Int).run.run = pure (some (.ok v)) := by
  obtain ⟨v, -, h⟩ := run_run_liftRustM_of_panicFreeOn (spec := unifSpec) incrIndex_panicFreeOn hp
  exact ⟨v, h⟩

example (p : Array Int × Int) :
    Triple (liftRustM (incrIndex p) : RustOracleComp unifSpec Int) (IncrIndexPre p)
      (fun _ => True) ((fun _ => False, fun _ => False, EStackEnd.mk) :
        EStack⟨CatCrypt.VCVio.Rust.Error → Prop, Unit → Prop⟩) :=
  triple_liftRustM_of_bot (incrIndex_triple p)

example (a b : Int) (h : 0 ≤ a + b ∧ a + b < 2 ^ 64) : ∃ r,
    (liftRustM (addM_w 64 a b) : RustOracleComp unifSpec Int).run.run =
      pure (some (.ok r)) := ⟨add a b, by rw [addM_w_of_guard 64 a b h]; rfl⟩

end HaxWPTest
