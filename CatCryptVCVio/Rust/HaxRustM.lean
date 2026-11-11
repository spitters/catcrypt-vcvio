/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Hax.RustM
public import CatCryptVCVio.Rust.OracleComp
public import VCVio.OracleComp.Coercions.SubSpec.Basic

/-!
# hax-lean's `RustM` inside `RustOracleComp`

hax-lean reads extracted Rust code into the deterministic result monad `RustM`
(`Aeneas.Std.RustM`: a value, a failure or divergence). `RustOracleComp spec` is the monad of
Rust code with access to the oracles of `spec`. This module lifts the former into the latter,
so that a deterministic extracted function is a term of `RustOracleComp spec` for every `spec`.

The lift sends a value to `ok`, a failure to `fail` at the corresponding error kind and
divergence to `div`; it is a monad morphism, and every lifted computation runs to a point mass
`pure (toOptionExcept x)`. Lifting into `RustOracleComp spec` and then along an oracle-spec
inclusion `spec → superSpec` (`RustOracleComp.liftSpec`, the query lift of VCVio applied under
both transformer layers) equals lifting directly into `RustOracleComp superSpec`. With
`spec = unifSpec`, a program over `ProbComp` that calls extracted code therefore lifts into any
larger oracle interface with the extracted calls unchanged.

## Main definitions

* `CatCrypt.VCVio.Rust.errorOfHax`: the error kinds of hax-lean as errors of `RustOracleComp`.
* `CatCrypt.VCVio.Rust.toOptionExcept`: a `RustM` result as `Option (Except Error α)`.
* `CatCrypt.VCVio.Rust.liftRustM`: the lift `RustM α → RustOracleComp spec α`, also a
  `MonadLift` instance.
* `CatCrypt.VCVio.Rust.RustOracleComp.liftSpec`: the lift of `RustOracleComp` along a
  query lift `OracleQuery spec → OracleQuery superSpec`.

## Main results

* `liftRustM_pure`, `liftRustM_bind`: `liftRustM` is a monad morphism.
* `run_run_liftRustM`: a lifted computation runs to `pure (toOptionExcept x)`.
* `RustOracleComp.liftSpec_liftRustM`: the square of `liftRustM` with `liftSpec`.
* `RustOracleComp.liftSpec_pure`, `liftSpec_bind`, `liftSpec_liftOracleComp`: `liftSpec` is a
  monad morphism extending VCVio's `liftComp`.
-/

public section

set_option autoImplicit false

namespace CatCrypt.VCVio.Rust

/-- The error kinds of hax-lean as errors of `RustOracleComp`: `panic` to `panic` and `undef`
to `undef`. -/
@[expose]
def errorOfHax : Aeneas.Std.Error → Error
  | .panic => .panic
  | .undef => .undef

/-- A `RustM` result in the run form of `RustOracleComp`: a value `v` is `some (.ok v)`, a
failure is `some (.error _)` and divergence is `none`. -/
@[expose]
def toOptionExcept {α : Type} : RustM α → Option (Except Error α)
  | .ok v => some (.ok v)
  | .fail e => some (.error (errorOfHax e))
  | .div => none

/-- The lift of a deterministic Rust computation of hax-lean into Rust computations with oracle
access: a value to `ok`, a failure to `fail` and divergence to `div`. -/
@[expose]
def liftRustM {ι : Type} {spec : OracleSpec ι} {α : Type} :
    RustM α → RustOracleComp spec α
  | .ok v => RustOracleComp.ok v
  | .fail e => RustOracleComp.fail (errorOfHax e)
  | .div => RustOracleComp.div

section liftRustM

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- A value lifts to `ok`. -/
@[simp]
theorem liftRustM_ok (v : α) :
    (liftRustM (.ok v) : RustOracleComp spec α) = RustOracleComp.ok v := rfl

/-- A failure lifts to `fail` at the corresponding error kind. -/
@[simp]
theorem liftRustM_fail (e : Aeneas.Std.Error) :
    (liftRustM (.fail e) : RustOracleComp spec α) = RustOracleComp.fail (errorOfHax e) := rfl

/-- Divergence lifts to `div`. -/
@[simp]
theorem liftRustM_div :
    (liftRustM .div : RustOracleComp spec α) = RustOracleComp.div := rfl

/-- `liftRustM` preserves `pure`. -/
@[simp]
theorem liftRustM_pure (v : α) :
    (liftRustM (pure v : RustM α) : RustOracleComp spec α) = pure v := rfl

/-- `liftRustM` preserves `bind`. -/
theorem liftRustM_bind (x : RustM α) (f : α → RustM β) :
    (liftRustM (x >>= f) : RustOracleComp spec β) =
      liftRustM x >>= fun a => liftRustM (f a) := by
  cases x <;> rfl

/-- A lifted `RustM` computation runs to the point mass at its `toOptionExcept` encoding. -/
@[simp]
theorem run_run_liftRustM (x : RustM α) :
    (liftRustM x : RustOracleComp spec α).run.run = pure (toOptionExcept x) := by
  cases x <;> rfl

/-- `liftRustM` as a monad lift. Nothing else lifts `RustM` into `RustOracleComp spec`: the
other lifts into `RustOracleComp spec` start at `OptionT (OracleComp spec)` or
`OracleComp spec`, and none of them is reached from `RustM`. -/
instance : MonadLift RustM (RustOracleComp spec) where
  monadLift := liftRustM

/-- The monad lift of a `RustM` computation is `liftRustM`. -/
@[simp]
theorem liftM_eq_liftRustM (x : RustM α) :
    (liftM x : RustOracleComp spec α) = liftRustM x := rfl

/-- `liftRustM` is a lawful monad lift. -/
instance : LawfulMonadLift RustM (RustOracleComp spec) where
  monadLift_pure := liftRustM_pure
  monadLift_bind := liftRustM_bind

end liftRustM

namespace RustOracleComp

section liftSpec

variable {ι τ : Type} {spec : OracleSpec ι} (superSpec : OracleSpec τ)
  [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] {α β : Type}

/-- The lift of a Rust computation with access to the oracles of `spec` along a query lift
into `superSpec`: VCVio's `OracleComp.liftComp` applied under the `OptionT` and `ExceptT`
layers. -/
@[expose]
def liftSpec (x : RustOracleComp spec α) : RustOracleComp superSpec α :=
  ExceptT.mk (OptionT.mk (OracleComp.liftComp x.run.run superSpec))

/-- `liftSpec` runs to the `liftComp` of the run. -/
@[simp]
theorem run_run_liftSpec (x : RustOracleComp spec α) :
    (liftSpec superSpec x).run.run = OracleComp.liftComp x.run.run superSpec := rfl

/-- `liftSpec` preserves `pure`. -/
@[simp]
theorem liftSpec_pure (v : α) :
    liftSpec superSpec (pure v : RustOracleComp spec α) = pure v := rfl

/-- `liftSpec` preserves `bind`. -/
theorem liftSpec_bind (x : RustOracleComp spec α) (f : α → RustOracleComp spec β) :
    liftSpec superSpec (x >>= f) = liftSpec superSpec x >>= fun a => liftSpec superSpec (f a) := by
  apply ExceptT.ext
  apply OptionT.ext
  simp only [liftSpec, ExceptT.run_bind, OptionT.run_bind, Option.elimM, OracleComp.liftComp_bind,
    ExceptT.run_mk, OptionT.run_mk]
  refine bind_congr fun o => ?_
  rcases o with _ | _ | _ <;> rfl

/-- `liftSpec` sends a lifted oracle computation to the lift of its `liftComp`. -/
@[simp]
theorem liftSpec_liftOracleComp (oa : OracleComp spec α) :
    liftSpec superSpec (liftOracleComp oa) = liftOracleComp (OracleComp.liftComp oa superSpec) := by
  aesop

/-- Lifting a `RustM` computation into `RustOracleComp spec` and then along the query lift into
`superSpec` equals lifting it directly into `RustOracleComp superSpec`. -/
@[simp]
theorem liftSpec_liftRustM (x : RustM α) :
    liftSpec superSpec (liftRustM x : RustOracleComp spec α) = liftRustM x := by
  cases x <;> rfl

/-- The square of `liftSpec_liftRustM` at `spec = unifSpec`, for a probabilistic program that
calls extracted code: a `ProbComp`-level Rust program `x >>= f`, whose first step is a
deterministic extracted call, lifts into `superSpec` as the extracted call followed by the
lifted continuation. -/
theorem liftSpec_liftRustM_bind [MonadLiftT (OracleQuery unifSpec) (OracleQuery superSpec)]
    (x : RustM α) (f : α → RustOracleComp unifSpec β) :
    liftSpec superSpec (liftRustM x >>= f) =
      liftRustM x >>= fun a => liftSpec superSpec (f a) := by
  rw [liftSpec_bind, liftSpec_liftRustM]

end liftSpec

end RustOracleComp

end CatCrypt.VCVio.Rust
