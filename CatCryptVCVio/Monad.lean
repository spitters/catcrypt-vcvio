/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Prob.Support
public import CatCryptCore.Crypto.SDistrLift
public import VCVio

/-!
# VCVio Bridge — Monad layer

Probability-level and stateless monad-morphism bridge between VCVio and CatCrypt,
stated in `SDistr` / `SPComp` terms.

VCVio denotes a computation `mx` by the measure `𝒟[mx]` of its successful outputs
(`EvalDistSemantics`). CatCrypt's `SDistr α = PMF (Option α)` is a sub-probability
mass function, `none` carrying the failure mass. This module gives `SDistr` the
measure semantics `𝒟[d] = ∑ₓ d (some x) • δₓ`, which embeds the sub-PMF monad into
the Giry monad, and interprets VCVio's `ProbComp` in `SDistr` by answering each
uniform query with `SDistr.uniform`.

## Main definitions

* `sdistrMeasure` — the measure of successful outputs of an `SDistr`, and the
  instances `EvalDistSemantics SDistr`, `LawfulEvalDistSemantics SDistr`
* `unifImpl` — the uniform-query handler `QueryImpl unifSpec SDistr`
* `ProbComp.toSDistr` — `simulateQ unifImpl`, the interpretation of `ProbComp` in `SDistr`
* `probCompLift` — `ProbComp → SPComp` monad morphism, composing `ProbComp.toSDistr`
  with the core lift `CatCrypt.Crypto.SDistrLift.sdistrToSPComp`

## Main results

* `evalDist_sdistr_singleton` — `𝒟[d] {x} = d (some x)` under `MeasurableSingletonClass`
* `evalDist_sdistr_injective` — `d ↦ 𝒟[d]` is injective under `MeasurableSingletonClass`
* `evalDist_toSDistr` — `𝒟[mx] = 𝒟[ProbComp.toSDistr mx]` for every `mx : ProbComp α`
* `probCompLift_pure` / `probCompLift_bind` — monad-morphism laws for `ProbComp`
* `probCompLift_isPure` — the ProbComp lift ignores the heap argument
-/

@[expose] public section

namespace CatCrypt.Crypto.VCVioBridge

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.SDistrLift
open MeasureTheory
open scoped ENNReal

universe u

/-! ## Measure semantics of `SDistr` -/

/-- The measure of successful outputs of a sub-distribution: the weighted sum of
    Dirac measures `∑ₓ d (some x) • δₓ`. The failure mass `d none` is dropped. -/
noncomputable def sdistrMeasure {α : Type u} [MeasurableSpace α] (d : SDistr α) :
    Measure α :=
  Measure.sum fun x => d (some x) • Measure.dirac x

/-- The value of `sdistrMeasure d` on a measurable set is the mass of its points. -/
theorem sdistrMeasure_apply {α : Type u} [MeasurableSpace α] (d : SDistr α)
    {s : Set α} (hs : MeasurableSet s) :
    sdistrMeasure d s = ∑' x, d (some x) * s.indicator 1 x := by
  simp [sdistrMeasure, Measure.sum_apply _ hs, Measure.dirac_apply' _ hs]

/-- The success mass of a sub-distribution is at most one. -/
theorem sdistrMeasure_apply_univ_le_one {α : Type u} [MeasurableSpace α] (d : SDistr α) :
    sdistrMeasure d Set.univ ≤ 1 := by
  rw [sdistrMeasure_apply d MeasurableSet.univ]
  simpa using (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective α) d).trans_eq
    (PMF.tsum_coe d)

/-- `SDistr` denotes its successful outputs by `sdistrMeasure`. -/
noncomputable instance instEvalDistSemanticsSDistr : EvalDistSemantics SDistr where
  denote d := sdistrMeasure d
  apply_univ_le_one d := sdistrMeasure_apply_univ_le_one d

/-- Unfolding lemma of `instEvalDistSemanticsSDistr`. -/
theorem evalDist_sdistr {α : Type u} [MeasurableSpace α] (d : SDistr α) :
    𝒟[d] = sdistrMeasure d := rfl

/-- `SDistr.pure` denotes a Dirac measure. -/
theorem sdistrMeasure_pure {α : Type u} [MeasurableSpace α] (x : α) :
    sdistrMeasure (SDistr.pure x) = Measure.dirac x := by
  ext s hs
  rw [sdistrMeasure_apply _ hs, Measure.dirac_apply' _ hs,
    tsum_eq_single x (fun b hb => by simp [SDistr.pure, hb])]
  simp [SDistr.pure]

/-- `SDistr.bind` denotes the Giry bind for a measurable continuation. -/
theorem sdistrMeasure_bind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (d : SDistr α) (f : α → SDistr β) (hf : Measurable fun x => sdistrMeasure (f x)) :
    sdistrMeasure (SDistr.bind d f) = (sdistrMeasure d).bind fun x => sdistrMeasure (f x) := by
  have hbind : ∀ y, SDistr.bind d f (some y) = ∑' x, d (some x) * f x (some y) := by
    intro y
    rw [SDistr.bind, PMF.bind_apply, tsum_option_split]
    simp [SDistr.fail_apply_some]
  ext s hs
  rw [Measure.bind_apply hs hf.aemeasurable, sdistrMeasure_apply _ hs]
  conv_rhs => rw [sdistrMeasure, lintegral_sum_measure]
  have hm : Measurable fun a => sdistrMeasure (f a) s := (Measure.measurable_coe hs).comp hf
  simp only [lintegral_smul_measure]
  simp only [lintegral_dirac' _ hm]
  simp only [sdistrMeasure_apply _ hs, hbind]
  simp_rw [← ENNReal.tsum_mul_right, smul_eq_mul, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

instance instLawfulEvalDistSemanticsSDistr : LawfulEvalDistSemantics SDistr where
  denote_pure x := sdistrMeasure_pure x
  denote_bind d f hf := sdistrMeasure_bind d f hf

/-- On a type with measurable singletons, the mass of `{x}` is the probability of `some x`. -/
theorem evalDist_sdistr_singleton {α : Type u} [MeasurableSpace α] [MeasurableSingletonClass α]
    (d : SDistr α) (x : α) : 𝒟[d] {x} = d (some x) := by
  rw [evalDist_sdistr, sdistrMeasure_apply _ (measurableSet_singleton x),
    tsum_eq_single x (fun b hb => by simp [hb])]
  simp

/-- On a type with measurable singletons, a sub-distribution is determined by its
    measure of successful outputs: the sub-PMF monad embeds into the Giry monad. -/
theorem evalDist_sdistr_injective {α : Type u} [MeasurableSpace α] [MeasurableSingletonClass α] :
    Function.Injective (fun d : SDistr α => 𝒟[d]) := by
  intro d₁ d₂ h
  have hs : ∀ x, d₁ (some x) = d₂ (some x) := fun x => by
    rw [← evalDist_sdistr_singleton, ← evalDist_sdistr_singleton]
    exact congrArg (fun μ : Measure α => μ {x}) h
  have hn : d₁ none = d₂ none := by
    have h₁ := PMF.tsum_coe d₁
    have h₂ := PMF.tsum_coe d₂
    rw [tsum_option_split] at h₁ h₂
    simp only [hs] at h₁
    have hfin : ∑' x, d₂ (some x) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (h₂ ▸ le_add_self)
    exact (ENNReal.add_left_inj hfin).1 (h₁.trans h₂.symm)
  apply PMF.ext
  intro o
  cases o with
  | none => exact hn
  | some x => exact hs x

/-- The uniform sub-distribution on `Fin (n + 1)` denotes the uniform measure. -/
theorem evalDist_sdistr_uniform_fin (n : ℕ) :
    𝒟[SDistr.uniform (Fin (n + 1))] = ProbabilityTheory.uniformOn Set.univ := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [evalDist_sdistr_singleton, SDistr.uniform_apply_some, ProbabilityTheory.uniformOn_univ]
  simp

/-! ## ProbComp interpreted in SDistr -/

/-- The handler answering the uniform query `n` of `unifSpec` with the uniform
    sub-distribution on `Fin (n + 1)`. -/
noncomputable def unifImpl : QueryImpl unifSpec SDistr :=
  fun n => SDistr.uniform (Fin (n + 1))

/-- Interpret VCVio's `ProbComp` in `SDistr`: each uniform query is answered by
    `SDistr.uniform`. -/
noncomputable def ProbComp.toSDistr {α : Type} (mx : ProbComp α) : SDistr α :=
  simulateQ unifImpl mx

@[simp] theorem ProbComp.toSDistr_pure {α : Type} (a : α) :
    ProbComp.toSDistr (pure a : ProbComp α) = SDistr.pure a := rfl

@[simp] theorem ProbComp.toSDistr_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) :
    ProbComp.toSDistr (mx >>= f) =
      SDistr.bind (ProbComp.toSDistr mx) (fun a => ProbComp.toSDistr (f a)) :=
  simulateQ_bind unifImpl mx f

/-- VCVio's measure semantics of a `ProbComp` agrees with the measure semantics of its
    interpretation in `SDistr`. -/
theorem evalDist_toSDistr {α : Type} [MeasurableSpace α] (mx : ProbComp α) :
    𝒟[mx] = 𝒟[ProbComp.toSDistr mx] := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    rw [evalDist_pure, ProbComp.toSDistr_pure, evalDist_sdistr, sdistrMeasure_pure]
  | query_bind t oa ih =>
    have hq : ProbComp.toSDistr (liftM (OracleSpec.query t) : ProbComp (Fin (t + 1))) =
        SDistr.uniform (Fin (t + 1)) :=
      simulateQ_spec_query unifImpl t
    rw [evalDist_bind_of_discrete, ProbComp.toSDistr_bind, hq, evalDist_sdistr,
      sdistrMeasure_bind _ _ Measurable.of_discrete, ← evalDist_sdistr,
      evalDist_sdistr_uniform_fin, OracleComp.evalDist_liftM_unifSpec_query]
    congr 1
    funext x
    exact ih x

/-! ## ProbComp → SPComp monad morphism

The state-independent lift `sdistrToSPComp` and its monad-morphism laws are pure
CatCrypt content and live in `CatCryptCore.Crypto.SDistrLift`; only the
VCVio-specific `ProbComp` composition is kept here. -/

/-- Full monad morphism `ProbComp → SPComp`: run the `ProbComp` to an `SDistr`,
    then lift to `SPComp` by ignoring the heap. This is the canonical stateless
    embedding used throughout the bridge. -/
noncomputable def probCompLift {α : Type} (mx : ProbComp α) : SPComp α :=
  sdistrToSPComp (ProbComp.toSDistr mx)

@[simp] theorem probCompLift_eq {α : Type} (mx : ProbComp α) :
    probCompLift mx = sdistrToSPComp (ProbComp.toSDistr mx) := rfl

/-- `probCompLift` preserves `pure`. -/
theorem probCompLift_pure {α : Type} (a : α) :
    probCompLift (pure a : ProbComp α) = SPComp.pure a :=
  sdistrToSPComp_pure a

/-- `probCompLift` preserves `bind`. -/
theorem probCompLift_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) :
    probCompLift (mx >>= f) = SPComp.bind (probCompLift mx) (fun a => probCompLift (f a)) :=
  (congrArg sdistrToSPComp (ProbComp.toSDistr_bind mx f)).trans (sdistrToSPComp_bind _ _)

/-- The lift produces heap-independent (i.e. `IsPure`) computations. -/
theorem probCompLift_isPure {α : Type} (mx : ProbComp α) :
    SPComp.IsPure (probCompLift mx) :=
  sdistrToSPComp_isPure _

end CatCrypt.Crypto.VCVioBridge
