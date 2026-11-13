/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Rust.HaxSignature

/-!
# hax-lean's `RustM` as the Rust programs that fail at hax errors

`toRustProg` reads a `RustM` computation as a Rust program without oracles, and its
interpretation `RustProg.interpHax` into `RustM` is a left inverse of it
(`CatCryptVCVio.Rust.HaxSignature`). The errors of `RustOracleComp` are finer than those of
hax-lean: `errorOfHax` reaches `panic` and `undef` only. A Rust program without oracles is the
image of a `RustM` computation exactly when its failure operation, if any, is at an error in the
image of `errorOfHax`; on these programs `toRustProg` undoes `interpHax`, and the two maps form
an equivalence between `RustM α` and the subtype of these programs.

## Main definitions

* `CatCrypt.VCVio.Rust.Error.IsHax`: an error in the image of `errorOfHax`.
* `CatCrypt.VCVio.Rust.RustProg.FailsAtHax`: a Rust program without oracles whose failure
  operation is at an error in the image of `errorOfHax`.
* `CatCrypt.VCVio.Rust.RustProg.haxEquiv`: the equivalence
  `RustM α ≃ {p : RustProg spec₀ α // FailsAtHax p}`, with `toRustProg` forward and
  `interpHax` backward.

## Main results

* `RustProg.failsAtHax_toRustProg`: the image of `toRustProg` fails at hax errors.
* `RustProg.toRustProg_interpHax`: on a program failing at hax errors, `toRustProg` undoes
  `interpHax`.
* `RustProg.toRustProg_interpHax_eq_iff`: `toRustProg (interpHax p) = p` exactly when `p` fails
  at hax errors.
* `RustProg.failsAtHax_iff_exists`: a program fails at hax errors exactly when it is the image
  of a `RustM` computation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.VCVio.Rust

open PFunctor

/-- An error of `RustOracleComp` is a hax error when it is the image of a hax-lean error under
`errorOfHax`. -/
def Error.IsHax (e : Error) : Prop := ∃ e' : Aeneas.Std.Error, errorOfHax e' = e

/-- Every image of `errorOfHax` is a hax error. -/
theorem Error.isHax_errorOfHax (e : Aeneas.Std.Error) : Error.IsHax (errorOfHax e) :=
  ⟨e, rfl⟩

namespace RustProg

variable {spec₀ : OracleSpec PEmpty} {α : Type}

/-- A Rust program without oracles fails at hax errors when it is `pure`, the divergence
operation, or the failure operation at a hax error. -/
def FailsAtHax : RustProg spec₀ α → Prop
  | .pure _ => True
  | .liftBind (.inl (.inl e)) _ => Error.IsHax e
  | .liftBind (.inl (.inr _)) _ => True
  | .liftBind (.inr t) _ => PEmpty.elim t

/-- The image of `toRustProg` fails at hax errors. -/
theorem failsAtHax_toRustProg (x : RustM α) : FailsAtHax (toRustProg x : RustProg spec₀ α) := by
  cases x
  · trivial
  · exact Error.isHax_errorOfHax _
  · trivial

/-- On a program failing at hax errors, `toRustProg` undoes `interpHax`. -/
theorem toRustProg_interpHax (p : RustProg spec₀ α) (hp : FailsAtHax p) :
    toRustProg (interpHax p) = p := by
  match p, hp with
  | .pure _, _ => rfl
  | .liftBind (.inl (.inl e)) k, ⟨e', he⟩ =>
    subst he
    cases e' <;> exact congrArg (FreeM.liftBind _) (funext fun x => PEmpty.elim x)
  | .liftBind (.inl (.inr PUnit.unit)) k, _ =>
    exact congrArg (FreeM.liftBind _) (funext fun x => PEmpty.elim x)
  | .liftBind (.inr t) _, _ => exact PEmpty.elim t

/-- `toRustProg (interpHax p) = p` exactly when `p` fails at hax errors. -/
theorem toRustProg_interpHax_eq_iff (p : RustProg spec₀ α) :
    toRustProg (interpHax p) = p ↔ FailsAtHax p := by
  refine ⟨fun h => ?_, toRustProg_interpHax p⟩
  rw [← h]
  exact failsAtHax_toRustProg _

/-- A program fails at hax errors exactly when it is the image of a `RustM` computation. -/
theorem failsAtHax_iff_exists (p : RustProg spec₀ α) :
    FailsAtHax p ↔ ∃ x : RustM α, toRustProg x = p := by
  refine ⟨fun hp => ⟨interpHax p, toRustProg_interpHax p hp⟩, ?_⟩
  rintro ⟨x, rfl⟩
  exact failsAtHax_toRustProg x

/-- hax-lean's `RustM α` is equivalent to the Rust programs without oracles that fail at hax
errors: `toRustProg` forward and `interpHax` backward. -/
def haxEquiv : RustM α ≃ {p : RustProg spec₀ α // FailsAtHax p} where
  toFun x := ⟨toRustProg x, failsAtHax_toRustProg x⟩
  invFun p := interpHax p.1
  left_inv x := interpHax_toRustProg x
  right_inv p := Subtype.ext (toRustProg_interpHax p.1 p.2)

end RustProg

end CatCrypt.VCVio.Rust
