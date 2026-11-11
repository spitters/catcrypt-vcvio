/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Rust.OracleComp
public import PolyFun.PFunctor.Handler.Sum

/-!
# Rust effects as a polynomial signature

Rust's effects form the polynomial signature `rustSig = C Error + 1`: a failure operation
at each `e : Error` and one divergence operation, neither with an answer. A Rust program with
access to the oracles of `spec` is a term of PolyFun's free monad over
`rustSig + spec.toPFunctor`. An interpretation of these programs is a PolyFun handler of the
signature, and its fold `PFunctor.FreeM.liftM` is the unique monad morphism extending it.

Two handlers are given. `handler` interprets the programs into `RustOracleComp spec`, which
keeps panics and divergence apart; its equations on the operations are the run lemmas of
`CatCryptVCVio.Rust.OracleComp`. `failHandler` interprets them into
`OptionT (OracleComp spec)`, where a panic and divergence are both failure, and its fold is
the fold of `handler` followed by the monad morphism `RustOracleComp.toOptionT`.

## Main definitions

* `CatCrypt.VCVio.Rust.rustSig`: the signature of Rust's effects.
* `CatCrypt.VCVio.Rust.RustProg`: Rust programs with oracle access, `FreeM (rustSig + spec)`,
  with the operations `RustProg.fail`, `RustProg.div`, `RustProg.query` and the embedding
  `RustProg.liftOracleComp`.
* `CatCrypt.VCVio.Rust.RustProg.handler`, `RustProg.interp`, `RustProg.interpHom`: the
  interpretation into `RustOracleComp spec`.
* `CatCrypt.VCVio.Rust.RustOracleComp.toOptionT`: the monad morphism identifying panics with
  divergence.
* `CatCrypt.VCVio.Rust.RustProg.failHandler`, `RustProg.interpFail`: the interpretation into
  `OptionT (OracleComp spec)`.

## Main results

* `RustProg.interp_pure`, `RustProg.interp_bind`: the interpretation is a monad morphism.
* `RustProg.interp_fail`, `interp_div`, `interp_query_bind`, `interp_liftOracleComp`: the
  handler's equations on the operations, and `run_run_interp_fail`, `run_run_interp_div`,
  `run_run_interp_query_bind`, `run_run_interp_liftOracleComp_bind` in run form.
* `RustOracleComp.run_toOptionT`: `toOptionT` sends a panic outcome to `none`.
* `RustProg.interpFail_eq_toOptionT_interp`, `run_interpFail`: the failure-only interpretation
  factors through `interp`.
* `RustProg.interpFail_pure`, `interpFail_bind`, `interpFail_fail`, `interpFail_div`,
  `interpFail_query_bind`, `interpFail_liftOracleComp`: the failure-only interpretation is a
  monad morphism, with its equations on the operations.
-/

@[expose] public section

namespace CatCrypt.VCVio.Rust

open PFunctor

/-- The signature of Rust's effects: the failure operations `C Error`, one at each error and
with no answer, and the divergence operation `1 = C PUnit`, with no answer. -/
@[reducible]
def rustSig : PFunctor.{0, 0} := PFunctor.C Error + 1

/-- Rust programs with access to the oracles of `spec`: PolyFun's free monad over the sum of
Rust's effects and the oracle signature of `spec`. -/
abbrev RustProg {ι : Type} (spec : OracleSpec ι) (α : Type) : Type :=
  FreeM (rustSig + spec.toPFunctor) α

namespace RustProg

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- A panicking program: the failure operation at `e`. -/
def fail (e : Error) : RustProg spec α :=
  FreeM.liftBind (P := rustSig + spec.toPFunctor) (.inl (.inl e)) PEmpty.elim

/-- A diverging program: the divergence operation. -/
def div : RustProg spec α :=
  FreeM.liftBind (P := rustSig + spec.toPFunctor) (.inl (.inr PUnit.unit)) PEmpty.elim

/-- The query of the oracle at `t`. -/
def query (t : ι) : RustProg spec (spec t) :=
  FreeM.lift (P := rustSig + spec.toPFunctor) (.inr t)

/-- An oracle computation as a Rust program, relabelled along the right injection. -/
def liftOracleComp (oa : OracleComp spec α) : RustProg spec α :=
  FreeM.mapLens Lens.inr (OracleComp.toFreeM oa)

/-! ### The interpretation into `RustOracleComp` -/

/-- The handler of Rust's effects in `RustOracleComp spec`: failure at `e` is a panic with
error `e`, and divergence is divergence. -/
def rustHandler : Handler (RustOracleComp spec) rustSig
  | .inl e => RustOracleComp.fail e
  | .inr _ => RustOracleComp.div

/-- The handler of oracle queries in `RustOracleComp spec`: the lifted query. -/
def oracleHandler : Handler (RustOracleComp spec) spec.toPFunctor :=
  fun t => liftM (OracleComp.ofFreeM (FreeM.lift (P := spec.toPFunctor) t))

/-- The handler of the full signature in `RustOracleComp spec`. -/
def handler : Handler (RustOracleComp spec) (rustSig + spec.toPFunctor) :=
  Handler.sum rustHandler oracleHandler

/-- The interpretation of Rust programs in `RustOracleComp spec`: the fold of `handler`. -/
def interp (p : RustProg spec α) : RustOracleComp spec α :=
  FreeM.liftM handler p

/-- The interpretation as a bundled monad morphism. -/
def interpHom : (RustProg spec) →ᵐ (RustOracleComp spec) :=
  FreeM.liftMHom handler

@[simp]
theorem interpHom_apply (p : RustProg spec α) : interpHom p = interp p := rfl

/-- The interpretation preserves `pure`. -/
@[simp]
theorem interp_pure (v : α) : interp (pure v : RustProg spec α) = pure v :=
  interpHom.mmap_pure v

/-- The interpretation preserves `bind`. -/
@[simp]
theorem interp_bind (p : RustProg spec α) (k : α → RustProg spec β) :
    interp (p >>= k) = interp p >>= fun a => interp (k a) :=
  interpHom.mmap_bind p k

/-- The failure operation is interpreted as a panic. -/
@[simp]
theorem interp_fail (e : Error) : interp (fail e : RustProg spec α) = RustOracleComp.fail e := by
  rfl

/-- The divergence operation is interpreted as divergence. -/
@[simp]
theorem interp_div : interp (div : RustProg spec α) = RustOracleComp.div := by
  rfl

/-- A query followed by a continuation is interpreted as the lifted query followed by the
interpreted continuation. -/
@[simp]
theorem interp_query_bind (t : ι) (k : spec t → RustProg spec β) :
    interp (query t >>= k) =
      liftM (OracleComp.ofFreeM (FreeM.lift (P := spec.toPFunctor) t)) >>= fun a =>
        interp (k a) := by
  rfl

/-- An embedded oracle computation is interpreted as its lift. -/
@[simp]
theorem interp_liftOracleComp (oa : OracleComp spec α) :
    interp (liftOracleComp oa) = liftM oa := by
  rw [liftOracleComp, interp, handler, Handler.liftM_sum_mapLens_inr]
  have h := FreeM.liftM_natural (P := spec.toPFunctor) FreeM.lift
    (MonadHom.ofLift (OracleComp spec) (RustOracleComp spec)) (OracleComp.toFreeM oa)
  rw [FreeM.liftM_lift_eq_self] at h
  exact h.symm

/-! ### The run lemmas as equations of the interpretation -/

/-- `run_run_pure` for the interpretation. -/
theorem run_run_interp_pure (v : α) :
    (interp (pure v : RustProg spec α)).run.run =
      (pure (some (Except.ok v)) : OracleComp spec (Option (Except Error α))) := by
  simp

/-- `run_run_fail` for the interpretation. -/
theorem run_run_interp_fail (e : Error) :
    (interp (fail e : RustProg spec α)).run.run =
      (pure (some (Except.error e)) : OracleComp spec (Option (Except Error α))) := by
  simp

/-- `run_run_div` for the interpretation. -/
theorem run_run_interp_div :
    (interp (div : RustProg spec α)).run.run =
      (pure none : OracleComp spec (Option (Except Error α))) := by
  simp

/-- `run_run_bind_liftM` for the interpretation, at an embedded oracle computation. -/
theorem run_run_interp_liftOracleComp_bind (oa : OracleComp spec α)
    (k : α → RustProg spec β) :
    (interp (liftOracleComp oa >>= k)).run.run = oa >>= fun a => (interp (k a)).run.run := by
  simp

/-- `run_run_bind_liftM` for the interpretation, at a query. -/
theorem run_run_interp_query_bind (t : ι) (k : spec t → RustProg spec β) :
    (interp (query t >>= k)).run.run =
      OracleComp.ofFreeM (FreeM.lift (P := spec.toPFunctor) t) >>= fun a =>
        (interp (k a)).run.run := by
  rw [interp_query_bind, RustOracleComp.run_run_bind_liftM]

end RustProg

/-! ### Identifying panics with divergence -/

namespace RustOracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- The map from `RustOracleComp spec` to `OptionT (OracleComp spec)` that sends a panic to
failure and keeps divergence and results. -/
def toOptionTFun (x : RustOracleComp spec α) : OptionT (OracleComp spec) α :=
  x.run >>= fun r => match r with
    | .ok a => pure a
    | .error _ => failure

/-- `toOptionTFun` is a monad morphism. -/
def toOptionT : (RustOracleComp spec) →ᵐ (OptionT (OracleComp spec)) where
  toFun _ := toOptionTFun
  toFun_pure' _ := by grind [toOptionTFun]
  toFun_bind' _ _ := by
    simp only [toOptionTFun, ExceptT.run_bind, bind_assoc]
    refine bind_congr fun r => ?_
    cases r <;> simp

@[simp]
theorem toOptionT_apply (x : RustOracleComp spec α) : toOptionT x = toOptionTFun x := rfl

/-- In run form, `toOptionT` maps a panic outcome to `none`. -/
theorem run_toOptionT (x : RustOracleComp spec α) :
    (toOptionT x).run = (fun o => o.bind fun r => r.toOption) <$> x.run.run := by
  simp only [toOptionT_apply, toOptionTFun, OptionT.run_bind, Option.elimM, map_eq_bind_pure_comp]
  refine bind_congr fun o => ?_
  rcases o with _ | (_ | _) <;> rfl

end RustOracleComp

namespace RustProg

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-! ### The failure-only interpretation -/

/-- The handler of the full signature in `OptionT (OracleComp spec)`: failure and divergence
are both `failure`, and a query is the lifted query. -/
def failHandler : Handler (OptionT (OracleComp spec)) (rustSig + spec.toPFunctor) :=
  Handler.sum (fun _ => failure)
    (fun t => liftM (OracleComp.ofFreeM (FreeM.lift (P := spec.toPFunctor) t)))

/-- The interpretation of Rust programs in `OptionT (OracleComp spec)`. -/
def interpFail (p : RustProg spec α) : OptionT (OracleComp spec) α :=
  FreeM.liftM failHandler p

/-- The failure-only handler is `handler` followed by `RustOracleComp.toOptionT`. -/
theorem failHandler_eq :
    (failHandler : Handler (OptionT (OracleComp spec)) (rustSig + spec.toPFunctor)) =
      fun a => RustOracleComp.toOptionT (handler a) := by
  funext a
  rcases a with (_ | _) | _ <;> rfl

/-- The failure-only interpretation is the interpretation into `RustOracleComp spec` followed
by `RustOracleComp.toOptionT`. -/
theorem interpFail_eq_toOptionT_interp (p : RustProg spec α) :
    interpFail p = RustOracleComp.toOptionT (interp p) := by
  rw [interpFail, interp, FreeM.liftM_natural, failHandler_eq]

/-- In run form, the failure-only interpretation is the interpretation into
`RustOracleComp spec` with panics sent to `none`. -/
theorem run_interpFail (p : RustProg spec α) :
    (interpFail p).run = (fun o => o.bind fun r => r.toOption) <$> (interp p).run.run := by
  rw [interpFail_eq_toOptionT_interp, RustOracleComp.run_toOptionT]

/-- The failure-only interpretation preserves `pure`. -/
@[simp]
theorem interpFail_pure (v : α) : interpFail (pure v : RustProg spec α) = pure v :=
  (FreeM.liftMHom failHandler).mmap_pure v

/-- The failure-only interpretation preserves `bind`. -/
@[simp]
theorem interpFail_bind (p : RustProg spec α) (k : α → RustProg spec β) :
    interpFail (p >>= k) = interpFail p >>= fun a => interpFail (k a) :=
  (FreeM.liftMHom failHandler).mmap_bind p k

/-- A query followed by a continuation is interpreted as the lifted query followed by the
interpreted continuation. -/
@[simp]
theorem interpFail_query_bind (t : ι) (k : spec t → RustProg spec β) :
    interpFail (query t >>= k) =
      liftM (OracleComp.ofFreeM (FreeM.lift (P := spec.toPFunctor) t)) >>= fun a =>
        interpFail (k a) :=
  rfl

/-- An embedded oracle computation is interpreted as its lift. -/
@[simp]
theorem interpFail_liftOracleComp (oa : OracleComp spec α) :
    interpFail (liftOracleComp oa) = liftM oa := by
  rw [liftOracleComp, interpFail, failHandler, Handler.liftM_sum_mapLens_inr]
  have h := FreeM.liftM_natural (P := spec.toPFunctor) FreeM.lift
    (MonadHom.ofLift (OracleComp spec) (OptionT (OracleComp spec))) (OracleComp.toFreeM oa)
  rw [FreeM.liftM_lift_eq_self] at h
  exact h.symm

/-- The failure operation is interpreted as `failure`. -/
@[simp]
theorem interpFail_fail (e : Error) : interpFail (fail e : RustProg spec α) = failure := by
  rfl

/-- The divergence operation is interpreted as `failure`. -/
@[simp]
theorem interpFail_div : interpFail (div : RustProg spec α) = failure := by
  rfl

end RustProg

end CatCrypt.VCVio.Rust
