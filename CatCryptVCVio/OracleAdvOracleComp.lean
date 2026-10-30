/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryFree
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import CatCryptCore.ForMathlib.PMFUniformDefs

/-!
# Oracle adversaries with uniform sampling as VCVio oracle computations

An oracle adversary `OracleAdv D R α` is a tree of the free monad of `AdvSig D R`
(`CatCryptCore.Crypto.OracleAdversaryFree`). A VCVio computation
`OracleComp (unifSpec + (D →ₒ R)) α` is a tree of the free monad of the polynomial functor of
`unifSpec + (D →ₒ R)`. The lens `unifLens D R` sends a uniform query `inl n` to the sampling
node `rand (Fin (n + 1)) (PMF.uniformFintype _)` and an oracle query `inr d` to the query
node `query d`; its image is the uniform fragment of `FreeM (AdvSig D R)`.

## Main definitions

* `advSpec D R` — the oracle specification `unifSpec + (D →ₒ R)`
* `unifLens D R` — the lens from the polynomial functor of `advSpec D R` to `AdvSig D R`
* `ofOracleComp` — the oracle adversary tree of a VCVio computation, `FreeM.mapLens unifLens`
* `IsUnifRand` — the uniform fragment: every sampling node samples uniformly from a `Fin (n + 1)`
* `toOracleComp` — the VCVio computation of a tree in the uniform fragment
* `advImpl O` — the query implementation in `StateT S PMF` that samples uniformly and asks the
  stateful oracle `O`

## Main results

* `isUnifRand_iff_exists` — the uniform fragment is the image of `ofOracleComp`
* `run_ofOracleComp`, `run_eq_simulateQ` — running an adversary of the uniform fragment against
  `O` is `simulateQ (advImpl O)` of its VCVio computation
* `isQueryBound_ofOracleComp`, `isQueryBound_iff_isQueryBoundP` — the query bound is VCVio's
  `IsQueryBoundP` for the predicate `Sum.isRight` (uniform queries are not counted)
* `isQueryBoundBy_ofOracleComp`, `isQueryBoundBy_iff_isQueryBound` — the weighted query bound is
  VCVio's `IsQueryBound` with cost `0` at uniform queries
-/

@[expose] public section

noncomputable section

namespace CatCrypt.Crypto.VCVioBridge

open PFunctor OracleSpec OracleComp

variable {D R : Type}

/-- The oracle specification of an adversary with uniform sampling and one oracle `D → R`. -/
abbrev advSpec (D R : Type) : OracleSpec (ℕ ⊕ D) := unifSpec + (D →ₒ R)

/-- The lens sending a uniform query `inl n` to sampling from the uniform distribution on
`Fin (n + 1)`, and an oracle query `inr d` to the query `d`. -/
def unifLens (D R : Type) : Lens (advSpec D R).toPFunctor (AdvSig D R) where
  toFunA
    | .inl n => .rand (Fin (n + 1)) (PMF.uniformFintype _)
    | .inr d => .query d
  toFunB
    | .inl _ => id
    | .inr _ => id

/-- The oracle adversary tree of a VCVio computation. -/
def ofOracleComp {α : Type} (oc : OracleComp (advSpec D R) α) : FreeM (AdvSig D R) α :=
  FreeM.mapLens (unifLens D R) oc

/-- The uniform fragment of `FreeM (AdvSig D R)`: every sampling node samples from the uniform
distribution on some `Fin (n + 1)`. -/
inductive IsUnifRand {α : Type} : FreeM (AdvSig D R) α → Prop
  /-- A leaf. -/
  | pure (a : α) : IsUnifRand (.pure a)
  /-- A uniform sampling node over `Fin (n + 1)`. -/
  | rand (n : ℕ) (k : Fin (n + 1) → FreeM (AdvSig D R) α) :
      (∀ b, IsUnifRand (k b)) →
        IsUnifRand (.liftBind (P := AdvSig D R) (.rand (Fin (n + 1)) (PMF.uniformFintype _)) k)
  /-- A query node. -/
  | query (d : D) (k : R → FreeM (AdvSig D R) α) :
      (∀ r, IsUnifRand (k r)) → IsUnifRand (.liftBind (P := AdvSig D R) (.query d) k)

/-- The uniform fragment is the image of `ofOracleComp`. -/
theorem isUnifRand_iff_exists {α : Type} (x : FreeM (AdvSig D R) α) :
    IsUnifRand x ↔ ∃ oc : OracleComp (advSpec D R) α, ofOracleComp oc = x := by
  constructor
  · intro h
    induction h with
    | pure a => exact ⟨FreeM.pure a, rfl⟩
    | rand n k _ ih =>
      choose f hf using ih
      exact ⟨FreeM.liftBind (P := (advSpec D R).toPFunctor) (.inl n) f, by
        simp only [ofOracleComp] at hf
        simp only [ofOracleComp, FreeM.mapLens_liftBind]
        exact congrArg _ (funext hf)⟩
    | query d k _ ih =>
      choose f hf using ih
      exact ⟨FreeM.liftBind (P := (advSpec D R).toPFunctor) (.inr d) f, by
        simp only [ofOracleComp] at hf
        simp only [ofOracleComp, FreeM.mapLens_liftBind]
        exact congrArg _ (funext hf)⟩
  · rintro ⟨oc, rfl⟩
    induction oc with
    | pure a => exact IsUnifRand.pure a
    | queryBind t r ih =>
      rcases t with n | d
      · exact IsUnifRand.rand n _ ih
      · exact IsUnifRand.query d _ ih

/-- The VCVio computation of a tree of the uniform fragment. -/
def toOracleComp {α : Type} (x : FreeM (AdvSig D R) α) (h : IsUnifRand x) :
    OracleComp (advSpec D R) α :=
  ((isUnifRand_iff_exists x).1 h).choose

/-- The tree of the VCVio computation of `x` is `x`. -/
@[simp] theorem ofOracleComp_toOracleComp {α : Type} (x : FreeM (AdvSig D R) α)
    (h : IsUnifRand x) : ofOracleComp (toOracleComp x h) = x :=
  ((isUnifRand_iff_exists x).1 h).choose_spec

/-! ## Running -/

/-- The query implementation in `StateT S PMF`: a uniform query `inl n` samples uniformly from
`Fin (n + 1)`, an oracle query `inr d` asks the stateful oracle `O`. -/
def advImpl {S : Type} (O : S → D → PMF (R × S)) : QueryImpl (advSpec D R) (StateT S PMF)
  | .inl n => fun s => (PMF.uniformFintype (Fin (n + 1))).bind fun b => PMF.pure (b, s)
  | .inr d => fun s => O s d

/-- Interpreting the tree of `oc` by `runHandler O` is simulating `oc` by `advImpl O`. -/
theorem liftM_runHandler_ofOracleComp {S α : Type} (O : S → D → PMF (R × S))
    (oc : OracleComp (advSpec D R) α) :
    FreeM.liftM (P := AdvSig D R) (OracleAdv.runHandler O) (ofOracleComp oc) =
      simulateQ (advImpl O) oc := by
  rw [ofOracleComp, FreeM.liftM_mapLens]
  unfold simulateQ
  congr 1
  funext t
  rcases t with n | d <;> exact id_map _

/-- Running the adversary of a VCVio computation `oc` against `O` is simulating `oc` by
`advImpl O`. -/
theorem run_ofOracleComp {S α : Type} (O : S → D → PMF (R × S))
    (oc : OracleComp (advSpec D R) α) (s : S) :
    OracleAdv.run O (OracleAdv.ofFreeM (ofOracleComp oc)) s =
      (simulateQ (advImpl O) oc).run s := by
  rw [OracleAdv.run_eq_liftM, OracleAdv.toFreeM_ofFreeM, liftM_runHandler_ofOracleComp]
  rfl

/-- Running an adversary of the uniform fragment against `O` is simulating its VCVio
computation by `advImpl O`. -/
theorem run_eq_simulateQ {S α : Type} (O : S → D → PMF (R × S)) (A : OracleAdv D R α)
    (h : IsUnifRand (OracleAdv.toFreeM A)) (s : S) :
    OracleAdv.run O A s = (simulateQ (advImpl O) (toOracleComp _ h)).run s := by
  rw [← run_ofOracleComp, ofOracleComp_toOracleComp, OracleAdv.ofFreeM_toFreeM]

/-! ## Query bounds -/

/-- A roll bound on the tree of `oc` is VCVio's query bound on `oc` with the checks and costs
pulled back along `unifLens`. -/
theorem isRollBound_ofOracleComp {α B : Type} (oc : OracleComp (advSpec D R) α) (b : B)
    (canRoll : AdvPos D → B → Prop) (cost : AdvPos D → B → B) :
    (ofOracleComp oc).IsRollBound b canRoll cost ↔
      oc.IsQueryBound b (fun t => canRoll ((unifLens D R).toFunA t))
        (fun t => cost ((unifLens D R).toFunA t)) := by
  induction oc generalizing b with
  | pure a => exact Iff.rfl
  | queryBind t r ih =>
    rcases t with n | d
    · exact and_congr Iff.rfl (forall_congr' fun y => ih y _)
    · exact and_congr Iff.rfl (forall_congr' fun y => ih y _)

/-- The query bound of the adversary of `oc` is VCVio's bound on the queries `inr d`. -/
theorem isQueryBound_ofOracleComp {α : Type} (oc : OracleComp (advSpec D R) α) (q : ℕ) :
    (OracleAdv.ofFreeM (ofOracleComp oc)).IsQueryBound q ↔
      oc.IsQueryBoundP (fun t => t.isRight = true) q := by
  rw [OracleAdv.isQueryBound_iff_isRollBound, OracleAdv.toFreeM_ofFreeM,
    isRollBound_ofOracleComp, isQueryBoundP_def]
  refine FreeM.isRollBound_congr (fun t b => ?_) (fun t b => ?_)
  · rcases t with n | d <;> simp [unifLens, AdvSig.posCost, Nat.one_le_iff_ne_zero]
  · rcases t with n | d <;> simp [unifLens, AdvSig.posCost]

/-- The query bound of an adversary of the uniform fragment is VCVio's bound on the queries
`inr d` of its computation. -/
theorem isQueryBound_iff_isQueryBoundP {α : Type} (A : OracleAdv D R α)
    (h : IsUnifRand (OracleAdv.toFreeM A)) (q : ℕ) :
    A.IsQueryBound q ↔ (toOracleComp _ h).IsQueryBoundP (fun t => t.isRight = true) q := by
  rw [← isQueryBound_ofOracleComp, ofOracleComp_toOracleComp, OracleAdv.ofFreeM_toFreeM]

/-- The weighted query bound of the adversary of `oc` is VCVio's query bound with cost `0` at a
uniform query and `cost d` at a query `inr d`. -/
theorem isQueryBoundBy_ofOracleComp {α : Type} (cost : D → ℕ)
    (oc : OracleComp (advSpec D R) α) (n : ℕ) :
    (OracleAdv.ofFreeM (ofOracleComp oc)).IsQueryBoundBy cost n ↔
      oc.IsQueryBound n (fun t b => Sum.elim (fun _ => 0) cost t ≤ b)
        (fun t b => b - Sum.elim (fun _ => 0) cost t) := by
  rw [OracleAdv.isQueryBoundBy_iff_isRollBound, OracleAdv.toFreeM_ofFreeM,
    isRollBound_ofOracleComp]
  refine FreeM.isRollBound_congr (fun t b => ?_) (fun t b => ?_)
  · rcases t with n | d <;> rfl
  · rcases t with n | d <;> rfl

/-- The weighted query bound of an adversary of the uniform fragment is VCVio's query bound on
its computation with cost `0` at a uniform query and `cost d` at a query `inr d`. -/
theorem isQueryBoundBy_iff_isQueryBound {α : Type} (cost : D → ℕ) (A : OracleAdv D R α)
    (h : IsUnifRand (OracleAdv.toFreeM A)) (n : ℕ) :
    A.IsQueryBoundBy cost n ↔
      (toOracleComp _ h).IsQueryBound n (fun t b => Sum.elim (fun _ => 0) cost t ≤ b)
        (fun t b => b - Sum.elim (fun _ => 0) cost t) := by
  rw [← isQueryBoundBy_ofOracleComp, ofOracleComp_toOracleComp, OracleAdv.ofFreeM_toFreeM]

end CatCrypt.Crypto.VCVioBridge

end
