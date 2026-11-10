/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.PolyFun.RelationalGraded
public import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Approximate relational triples as a graded relational algebra

VCVio's `ApproxRelTriple ε oa ob R`, defined by
`1 - ε ≤ eRelWP oa ob (RelPost.indicator R)`, is a graded relational algebra at
grades in `ℝ≥0∞`. Bind adds errors through `approxRelTriple_bind` (VCVio#1076).
On `OracleComp`, which cannot fail, this form is equivalent to an approximate coupling.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.VCVioBridge.XDijkstra

open scoped ENNReal
open OracleSpec OracleComp.ProgramLogic.Relational

universe u

variable {ι₁ ι₂ : Type u}
  {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{u, 0} ι₂}
  [AnswerMeasure spec₁] [AnswerMeasure spec₂]
  [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]

/-- VCVio's approximate relational triples form a relational algebra graded by error. -/
noncomputable instance instMAlgRelGradedApproxRelTriple :
    MAlgRelGraded ℝ≥0∞ (OracleComp spec₁) (OracleComp spec₂) Prop where
  grwp ε x y R := ApproxRelTriple ε x y R
  grwp_pure a b post := by
    apply propext
    simp only [ApproxRelTriple, tsub_zero, eRelWP_pure]
    by_cases h : post a b <;> simp [RelPost.indicator, h]
  grwp_mono {_ _ _ _ _ post post'} hpost h := by
    refine le_trans h (eRelWP_mono fun a b => ?_)
    by_cases h₁ : post a b
    · have h₂ : post' a b := hpost a b h₁
      simp [RelPost.indicator, h₁, h₂]
    · simp [RelPost.indicator, h₁]
  grwp_mono_grade x y post hg h := le_trans (tsub_le_tsub_left hg 1) h
  grwp_bind_le g h x y f k post hb := approxRelTriple_bind hb fun _ _ hR => hR

end CatCrypt.Crypto.VCVioBridge.XDijkstra
