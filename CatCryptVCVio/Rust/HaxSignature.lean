/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Rust.HaxRustM
public import CatCryptVCVio.Rust.Signature

/-!
# hax-lean's `RustM` as programs of the Rust-effect signature

hax-lean reads extracted Rust code into the result monad `RustM` (`Aeneas.Std.RustM`: a value,
a failure or divergence). This module reads such a computation as a program of the Rust-effect
signature `rustSig`: a value is `pure`, a failure is the failure operation at the corresponding
error and divergence is the divergence operation. The map `toRustProg` is a monad morphism, and
the lift `liftRustM` of `CatCryptVCVio.Rust.HaxRustM` is `toRustProg` followed by the
interpretation `RustProg.interp` of `CatCryptVCVio.Rust.Signature`.

`RustM` is itself an interpretation of the signature: `haxHandler` interprets Rust programs
without oracles (`RustProg spec` at an oracle spec over the empty index type) into `RustM`,
and its fold is a left inverse of `toRustProg`.

## Main definitions

* `CatCrypt.VCVio.Rust.toRustProg`: a `RustM` computation as a Rust program.
* `CatCrypt.VCVio.Rust.haxOfError`: the errors of `RustOracleComp` as hax-lean errors.
* `CatCrypt.VCVio.Rust.RustProg.haxHandler`, `RustProg.interpHax`: the interpretation of
  Rust programs without oracles into `RustM`.

## Main results

* `toRustProg_pure`, `toRustProg_bind`: `toRustProg` is a monad morphism.
* `interp_toRustProg`: `RustProg.interp (toRustProg x) = liftRustM x`.
* `interpFail_toRustProg`: the failure-only interpretation of `toRustProg x` is
  `RustOracleComp.toOptionT (liftRustM x)`.
* `RustProg.interpHax_toRustProg`: the interpretation into `RustM` undoes `toRustProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.VCVio.Rust

open PFunctor

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- A `RustM` computation as a Rust program: a value `v` is `pure v`, a failure at `e` is the
failure operation at `errorOfHax e` and divergence is the divergence operation. -/
def toRustProg : RustM α → RustProg spec α
  | .ok v => pure v
  | .fail e => RustProg.fail (errorOfHax e)
  | .div => RustProg.div

/-- `toRustProg` preserves `pure`. -/
@[simp]
theorem toRustProg_pure (v : α) : (toRustProg (pure v : RustM α) : RustProg spec α) = pure v :=
  rfl

/-- A failure operation absorbs every continuation. -/
theorem RustProg.fail_bind (e : Error) (k : α → RustProg spec β) :
    (RustProg.fail e : RustProg spec α) >>= k = RustProg.fail e :=
  congrArg (FreeM.liftBind (P := rustSig + spec.toPFunctor) (.inl (.inl e)))
    (funext fun x => PEmpty.elim x)

/-- The divergence operation absorbs every continuation. -/
theorem RustProg.div_bind (k : α → RustProg spec β) :
    (RustProg.div : RustProg spec α) >>= k = RustProg.div :=
  congrArg (FreeM.liftBind (P := rustSig + spec.toPFunctor) (.inl (.inr PUnit.unit)))
    (funext fun x => PEmpty.elim x)

/-- `toRustProg` preserves `bind`. -/
theorem toRustProg_bind (x : RustM α) (f : α → RustM β) :
    (toRustProg (x >>= f) : RustProg spec β) = toRustProg x >>= fun a => toRustProg (f a) := by
  cases x
  · rfl
  · exact (RustProg.fail_bind _ _).symm
  · exact (RustProg.div_bind _).symm

/-- `liftRustM` is `toRustProg` followed by the interpretation into `RustOracleComp spec`. -/
@[simp]
theorem interp_toRustProg (x : RustM α) :
    RustProg.interp (toRustProg x : RustProg spec α) = liftRustM x := by
  cases x
  · rfl
  · rfl
  · rfl

/-- The failure-only interpretation of `toRustProg x` is `liftRustM x` with panics sent to
failure. -/
theorem interpFail_toRustProg (x : RustM α) :
    RustProg.interpFail (toRustProg x : RustProg spec α) =
      RustOracleComp.toOptionT (liftRustM x) := by
  rw [RustProg.interpFail_eq_toOptionT_interp, interp_toRustProg]

/-- The errors of `RustOracleComp` as hax-lean errors: `undef` to `undef` and every other
error to `panic`. -/
def haxOfError : Error → Aeneas.Std.Error
  | .undef => .undef
  | _ => .panic

/-- `haxOfError` is a left inverse of `errorOfHax`. -/
@[simp]
theorem haxOfError_errorOfHax (e : Aeneas.Std.Error) : haxOfError (errorOfHax e) = e := by
  cases e <;> rfl

namespace RustProg

variable {spec₀ : OracleSpec PEmpty}

/-- The handler of the full signature in `RustM` at an oracle spec over the empty index type:
failure at `e` is `.fail (haxOfError e)`, divergence is `.div`, and there are no queries. -/
def haxHandler : Handler RustM (rustSig + spec₀.toPFunctor) :=
  Handler.sum (fun a => match a with
    | .inl e => .fail (haxOfError e)
    | .inr _ => .div)
    (fun t => PEmpty.elim t)

/-- The interpretation of Rust programs without oracles into `RustM`. -/
def interpHax (p : RustProg spec₀ α) : RustM α :=
  FreeM.liftM haxHandler p

/-- The interpretation into `RustM` undoes `toRustProg`. -/
@[simp]
theorem interpHax_toRustProg (x : RustM α) :
    interpHax (toRustProg x : RustProg spec₀ α) = x := by
  cases x
  · rfl
  · exact congrArg RustM.fail (haxOfError_errorOfHax _)
  · rfl

end RustProg

end CatCrypt.VCVio.Rust
