/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao

A copy of VCVio's `Interop/Rust/Common.lean` and `Interop/Rust/Run.lean` (Verified-zkEVM/VCVio,
main 8275ec2) in the namespace `CatCrypt.VCVio.Rust`. It does not import VCVio's `Interop`
package, whose `Aeneas.Std.RustM` cannot share an import closure with hax-lean's
`Aeneas.Std.RustM`.
-/

module

public import VCVio.OracleComp.OracleComp

/-!
# `RustOracleComp`: the target monad of Rust code with oracle access

```
RustOracleComp spec α  :=  ExceptT Error (OptionT (OracleComp spec)) α
```

The `ExceptT Error` layer models Rust panics, the `OptionT` layer models divergence, and the
`OracleComp spec` layer models probabilistic and oracle queries. Running both layers gives the
canonical form `OracleComp spec (Option (Except Error α))`; the `@[simp]` lemmas of the second
section reduce the common program shapes to it.

## Main definitions

* `CatCrypt.VCVio.Rust.Error`: the errors a Rust frontend reports.
* `CatCrypt.VCVio.Rust.RustOracleComp`: the transformer stack, with `ok`, `fail`, `div` and
  `liftOracleComp`.

## Main results

* `RustOracleComp.run_run_ok`, `run_run_fail`, `run_run_div`: the three constructors run to `pure`.
* `RustOracleComp.run_run_bind_liftM`: a lifted oracle call followed by a continuation runs to the
  underlying `OracleComp` bind.
-/

public section

namespace CatCrypt.VCVio.Rust

/-- The errors a Rust frontend reports. -/
inductive Error where
  | assertionFailure : Error
  | integerOverflow : Error
  | divisionByZero : Error
  | arrayOutOfBounds : Error
  | maximumSizeExceeded : Error
  | panic : Error
  | undef : Error
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Rust computations with oracle access: `OracleComp spec` for oracle access and probabilistic
semantics, `OptionT` for divergence (`none` is `div`), `ExceptT Error` for panics
(`some (.error e)` is `fail e`). A panicking computation does not diverge and a diverging one does
not return. -/
abbrev RustOracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type :=
  ExceptT Error (OptionT (OracleComp spec)) α

namespace RustOracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- A successful Rust computation. -/
@[expose, reducible, match_pattern]
def ok (v : α) : RustOracleComp spec α := pure v

/-- A panicking Rust computation. -/
@[expose, reducible, match_pattern]
def fail (e : Error) : RustOracleComp spec α := throw e

/-- A diverging Rust computation. -/
@[expose, reducible, match_pattern]
def div : RustOracleComp spec α :=
  ExceptT.mk (OptionT.mk (pure none))

/-- An oracle computation as a total, panic-free Rust computation. It is the two-step lift
`ExceptT.lift ∘ OptionT.lift`, so `vcgen` reaches it through core's `@[spec]` rules
`Std.WP.Spec.monadLift_OptionT` and `Std.WP.Spec.monadLift_ExceptT`. -/
@[expose, reducible]
def liftOracleComp (oa : OracleComp spec α) : RustOracleComp spec α :=
  ExceptT.lift (OptionT.lift oa)

/-! ### Running the constructors -/

/-- A successful Rust value runs to `pure (some (.ok v))`. -/
@[simp]
theorem run_run_ok (v : α) :
    (ok v : RustOracleComp spec α).run.run =
      (pure (some (Except.ok v)) : OracleComp spec (Option (Except Error α))) :=
  rfl

/-- `pure` runs to `pure (some (.ok v))`. -/
@[simp]
theorem run_run_pure (v : α) :
    ((pure v : RustOracleComp spec α)).run.run =
      (pure (some (Except.ok v)) : OracleComp spec (Option (Except Error α))) :=
  rfl

/-- A panic runs to `pure (some (.error e))`. -/
@[simp]
theorem run_run_fail (e : Error) :
    (fail e : RustOracleComp spec α).run.run =
      (pure (some (Except.error e)) : OracleComp spec (Option (Except Error α))) :=
  rfl

/-- `throw` runs to `pure (some (.error e))`. -/
@[simp]
theorem run_run_throw (e : Error) :
    ((throw e : RustOracleComp spec α)).run.run =
      (pure (some (Except.error e)) : OracleComp spec (Option (Except Error α))) :=
  rfl

/-- Divergence runs to `pure none`. -/
@[simp]
theorem run_run_div :
    (div : RustOracleComp spec α).run.run =
      (pure none : OracleComp spec (Option (Except Error α))) :=
  rfl

/-! ### Running a lifted oracle call -/

/-- A lifted oracle call followed by a continuation runs to the underlying `OracleComp` bind. -/
@[simp]
theorem run_run_bind_liftM (oa : OracleComp spec α) (k : α → RustOracleComp spec β) :
    ((liftM oa : RustOracleComp spec α) >>= k).run.run =
      oa >>= fun a => (k a).run.run := by
  change (ExceptT.run ((ExceptT.lift (OptionT.lift oa) : RustOracleComp spec α) >>= k)).run = _
  simp only [ExceptT.run_bind_lift, OptionT.run_bind_lift]

/-- A lifted oracle call runs to its values wrapped in `some (.ok _)`. -/
@[simp]
theorem run_run_liftM (oa : OracleComp spec α) :
    (liftM oa : RustOracleComp spec α).run.run = (fun a => some (Except.ok a)) <$> oa := by
  have h := run_run_bind_liftM (spec := spec) oa
    (k := fun a => (pure a : RustOracleComp spec α))
  simp only [bind_pure, run_run_pure] at h
  rw [h]
  exact (map_eq_pure_bind _ oa).symm

end RustOracleComp

end CatCrypt.VCVio.Rust
