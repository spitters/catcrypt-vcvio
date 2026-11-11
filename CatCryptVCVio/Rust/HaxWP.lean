/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Rust.HaxRustM
public import CatCryptCore.Crypto.UCMonad.RustMBridge
public import HaxLean.RuntimeM
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# hax-lean's `Std.WP` specifications over `RustOracleComp`

hax-lean interprets `RustM` in the toolchain's `Std.WP` logic (`HaxLean/RuntimeM.lean`): a value
satisfies the postcondition, a failure the exception postcondition, and divergence nothing. Its
guarded runtime operations (checked arithmetic, indexing, slicing, `unwrap`, `assert`) carry
`@[spec]` triples with the Rust guard as precondition.

`RustOracleComp spec = ExceptT Error (OptionT (OracleComp spec))` is interpreted by the core
`Std.WP` instances of `ExceptT` and `OptionT` over VCVio's necessary interpretation of
`OracleComp spec` (`OracleComp.Necessary.instWP`, every possible output), so its exception
postconditions are `EStack⟨Error → Prop, Unit → Prop⟩`: a postcondition on panics and one on
divergence. This module transfers hax-lean triples along `liftRustM`, which sends a failure to
`fail (errorOfHax e)` and divergence to `div`.

## Main results

* `wp_liftRustM_ok`, `wp_liftRustM_fail`, `wp_liftRustM_div`: the weakest precondition of a lifted
  computation.
* `triple_liftRustM`: a hax-lean triple `Triple x pre post epostH` gives the triple
  `Triple (liftRustM x) pre post epost` whenever `epostH e` implies `epost.1 (errorOfHax e)`.
* `triple_liftRustM_of_bot`: the same for a triple `⦃pre⦄ x ⦃post⦄`, at every `epost`.
* `addM_w_triple`, …, `assertM_triple`: the instances at the guarded operations that the monadic
  emitter of hax-lean (`HaxLean/MonadicEmit.lean`) prints in its regression programs.
* `triple_liftRustM_of_panicFreeOn`, `run_run_liftRustM_of_panicFreeOn`: a `RustM` function
  panic-free on `pre` lifts, at every argument satisfying `pre`, to a computation that neither
  panics nor diverges.

The panic-freedom results hold for every function `f : α → RustM β` with
`UCMonad.RustMBridge.PanicFreeOn pre f`. For a function accepted by the range checker of
hax-lean, that hypothesis is the statement about the `toRustMSB` reading of its extracted term
that the checker's soundness theorem gives; the results are about that reading.
-/

public section

set_option autoImplicit false

namespace CatCrypt.VCVio.Rust

open _root_.Std.WP Lean.Order
open scoped OracleComp.Necessary

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-! ### Weakest preconditions of lifted computations -/

/-- A lifted value satisfies the necessary weakest precondition exactly when it satisfies the
postcondition. -/
@[simp]
theorem wp_liftRustM_ok (v : α) (post : α → Prop) (epost : EStack⟨Error → Prop, Unit → Prop⟩) :
    wp (liftRustM (.ok v) : RustOracleComp spec α) post epost ↔ post v := by
  simp

/-- A lifted failure satisfies the necessary weakest precondition exactly when its error kind
satisfies the panic postcondition. -/
@[simp]
theorem wp_liftRustM_fail (e : Aeneas.Std.Error) (post : α → Prop)
    (epost : EStack⟨Error → Prop, Unit → Prop⟩) :
    wp (liftRustM (.fail e) : RustOracleComp spec α) post epost ↔ epost.1 (errorOfHax e) := by
  simp [ExceptT.wp_apply_eq]

/-- Lifted divergence satisfies the necessary weakest precondition exactly when the divergence
postcondition holds. -/
@[simp]
theorem wp_liftRustM_div (post : α → Prop) (epost : EStack⟨Error → Prop, Unit → Prop⟩) :
    wp (liftRustM .div : RustOracleComp spec α) post epost ↔ epost.2.1 () := by
  simp [ExceptT.wp_apply_eq, OptionT.wp_apply_eq]

/-! ### Transfer of triples -/

/-- **Transfer of hax-lean triples.** A `Std.WP` triple of hax-lean over `RustM` gives the triple
of the lifted computation over `RustOracleComp spec`, with the same precondition and
postcondition, when every error kind allowed by the hax-lean exception postcondition is allowed,
through `errorOfHax`, by the panic postcondition. The divergence postcondition is arbitrary:
hax-lean's interpretation is total, so a triple excludes divergence. -/
theorem triple_liftRustM {x : RustM α} {pre : Prop} {post : α → Prop}
    {epostH : Aeneas.Std.Error → Prop} {epost : EStack⟨Error → Prop, Unit → Prop⟩}
    (h : Triple x pre post epostH) (hE : ∀ e, epostH e → epost.1 (errorOfHax e)) :
    Triple (liftRustM x : RustOracleComp spec α) pre post epost := by
  refine ⟨fun hp => ?_⟩
  have hw := h.le_wp hp
  cases x with
  | ok v => exact (wp_liftRustM_ok v post epost).2 hw
  | fail e => exact (wp_liftRustM_fail e post epost).2 (hE e hw)
  | div => exact hw.elim

/-- **Transfer of hax-lean triples in the notation `⦃pre⦄ x ⦃post⦄`**, whose exception
postcondition `⊥` allows no error: the lifted triple holds at every panic and divergence
postcondition. -/
theorem triple_liftRustM_of_bot {x : RustM α} {pre : Prop} {post : α → Prop}
    {epost : EStack⟨Error → Prop, Unit → Prop⟩} (h : ⦃ pre ⦄ x ⦃ post ⦄) :
    Triple (liftRustM x : RustOracleComp spec α) pre post epost :=
  triple_liftRustM h fun _ hb => by simp_all

/-! ### The guarded operations -/

section Guarded

variable {epost : EStack⟨Error → Prop, Unit → Prop⟩}

/-- Checked unsigned addition: precondition no overflow. -/
theorem addM_w_triple (w : Nat) (a b : Int) :
    Triple (liftRustM (Hax.addM_w w a b) : RustOracleComp spec Int)
      (0 ≤ a + b ∧ a + b < 2 ^ w) (fun r => r = Hax.add a b) epost :=
  triple_liftRustM (Hax.addM_w_spec w a b) fun _ h => h

/-- Checked unsigned subtraction: precondition no underflow. -/
theorem subM_w_triple (w : Nat) (a b : Int) :
    Triple (liftRustM (Hax.subM_w w a b) : RustOracleComp spec Int)
      (0 ≤ a - b ∧ a - b < 2 ^ w) (fun r => r = Hax.sub a b) epost :=
  triple_liftRustM (Hax.subM_w_spec w a b) fun _ h => h

/-- Checked unsigned multiplication: precondition no overflow. -/
theorem mulM_w_triple (w : Nat) (a b : Int) :
    Triple (liftRustM (Hax.mulM_w w a b) : RustOracleComp spec Int)
      (0 ≤ a * b ∧ a * b < 2 ^ w) (fun r => r = Hax.mul a b) epost :=
  triple_liftRustM (Hax.mulM_w_spec w a b) fun _ h => h

/-- Unsigned division: precondition a nonzero divisor. -/
theorem divM_w_triple (w : Nat) (a b : Int) :
    Triple (liftRustM (Hax.divM_w w a b) : RustOracleComp spec Int)
      (b ≠ 0) (fun r => r = Hax.div a b) epost :=
  triple_liftRustM (Hax.divM_w_spec w a b) fun _ h => h

/-- Unsigned remainder: precondition a nonzero divisor. -/
theorem remM_w_triple (w : Nat) (a b : Int) :
    Triple (liftRustM (Hax.remM_w w a b) : RustOracleComp spec Int)
      (b ≠ 0) (fun r => r = Hax.rem a b) epost :=
  triple_liftRustM (Hax.remM_w_spec w a b) fun _ h => h

/-- Signed division: precondition a nonzero divisor and not `MIN / -1`. -/
theorem divM_iw_triple (w : Nat) (a b : Int) :
    Triple (liftRustM (Hax.divM_iw w a b) : RustOracleComp spec Int)
      (b ≠ 0 ∧ ¬(a = -2 ^ (w - 1) ∧ b = -1)) (fun r => r = Hax.div_iw w a b) epost :=
  triple_liftRustM (Hax.divM_iw_spec w a b) fun _ h => h

/-- Signed left shift: precondition an amount in `[0, w)`. -/
theorem shlM_iw_triple (w : Nat) (a b : Int) :
    Triple (liftRustM (Hax.shlM_iw w a b) : RustOracleComp spec Int)
      (0 ≤ b ∧ b < w) (fun r => r = Hax.shl_iw w a b) epost :=
  triple_liftRustM (Hax.shlM_iw_spec w a b) fun _ h => h

/-- Indexing: precondition an index within bounds. -/
theorem indexM_triple {γ : Type} [Inhabited γ] (a : Array γ) (i : Int) :
    Triple (liftRustM (Hax.indexM a i) : RustOracleComp spec γ)
      (0 ≤ i ∧ i < a.size) (fun r => r = Hax.index a i) epost :=
  triple_liftRustM (Hax.indexM_spec a i) fun _ h => h

/-- Slicing `a[lo..hi]`: precondition `0 ≤ lo ≤ hi ≤ a.size`. -/
theorem slice_rangeM_triple {γ : Type} (a : Array γ) (lo hi : Int) :
    Triple (liftRustM (Hax.slice_rangeM a lo hi) : RustOracleComp spec (Array γ))
      (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size) (fun r => r = Hax.slice_range a lo hi) epost :=
  triple_liftRustM (Hax.slice_rangeM_spec a lo hi) fun _ h => h

/-- `unwrap`: precondition `some`. -/
theorem unwrapM_triple {γ : Type} (o : Option γ) :
    Triple (liftRustM (Hax.unwrapM o) : RustOracleComp spec γ)
      (o.isSome = true) (fun r => o = some r) epost :=
  triple_liftRustM (Hax.unwrapM_spec o) fun _ h => h

/-- `assert`: precondition a true condition. -/
theorem assertM_triple (b : Bool) :
    Triple (liftRustM (Hax.assertM b) : RustOracleComp spec Unit)
      (b = true) (fun r => r = ()) epost :=
  triple_liftRustM (Hax.assertM_spec b) fun _ h => h

end Guarded

/-! ### Panic freedom -/

/-- A `RustM` function panic-free on `pre` lifts, at an argument satisfying `pre`, to a
computation whose panic and divergence postconditions are false. -/
theorem triple_liftRustM_of_panicFreeOn {pre : α → Prop} {f : α → RustM β}
    (hf : UCMonad.RustMBridge.PanicFreeOn pre f) (a : α) :
    Triple (liftRustM (f a) : RustOracleComp spec β) (pre a) (fun _ => True)
      ((fun _ => False, fun _ => False, EStackEnd.mk) : EStack⟨Error → Prop, Unit → Prop⟩) := by
  refine ⟨fun ha => ?_⟩
  obtain ⟨v, hv⟩ := hf a ha
  rw [hv]
  exact (wp_liftRustM_ok v _ _).2 trivial

/-- A `RustM` function panic-free on `pre` runs, at an argument satisfying `pre`, to the point
mass at a value: the lifted computation neither panics nor diverges. -/
theorem run_run_liftRustM_of_panicFreeOn {pre : α → Prop} {f : α → RustM β}
    (hf : UCMonad.RustMBridge.PanicFreeOn pre f) {a : α} (ha : pre a) :
    ∃ v, f a = .ok v ∧
      (liftRustM (f a) : RustOracleComp spec β).run.run = pure (some (.ok v)) := by
  obtain ⟨v, hv⟩ := hf a ha
  exact ⟨v, hv, by rw [hv]; rfl⟩

end CatCrypt.VCVio.Rust
