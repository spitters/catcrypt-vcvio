/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XStdWP
public import PolyFun.Control.Monad.ExactWP
public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.PFunctor.Free.WP.Upstream

/-!
# Exact PolyFun program logics as lawful XDijkstra observations

A `WPMonad m Pred EPred` instance is observed as an `XCoreWP` at grade type `Unit` by
`XCoreWP.ofWPMonad`, and the observation is lawful exactly when the laws of `pure` and
`bind` hold with equality. PolyFun's `ExactWPMonad` mixin states the reverse inequalities,
so every exact interpretation is a lawful observation. Two exact interpretations of
PolyFun are instances: the interpretation `MAlgOrdered.toWPMonad` of an ordered monad
algebra over a Mathlib complete lattice, whose weakest precondition of `x` at `post` is
`μ (x >>= fun a => pure (post a))`, and the interpretation `OpSpec.toWPMonad` of free
programs over a monotone per-operation specification, whose weakest precondition is the
fold `FreeM.wpFold`. Mathlib's `≤` agrees with `⊑` on a Mathlib complete lattice carrying
PolyFun's order bridge and on the empty exception postcondition `EStack⟨⟩`.

## Main results

* `lawfulXCoreWP_ofExactWPMonad`: the observation of an exact `WPMonad` is lawful.
* `instLERelCompatOfCompleteLattice`, `instLERelCompatUnit`: `≤` agrees with `⊑` on a
  Mathlib complete lattice and on `EStack⟨⟩`.
* `lawfulXCoreWP_ofMAlgOrdered`, `ofMAlgOrdered_wp`, `ofMAlgOrdered_triple_iff`: the
  observation of an ordered monad algebra is lawful, its weakest precondition is the
  algebra of the mapped program, and its triples are lower bounds of that algebra.
* `lawfulXCoreWP_ofOpSpec`, `ofOpSpec_wp`: the observation of free programs under a
  monotone per-operation specification is lawful, and its weakest precondition is
  `FreeM.wpFold`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.VCVioBridge.XDijkstra

open CatCrypt.XDijkstra CatCrypt.StdWPBridge Std.WP

universe u v w w' uA uB

/-! ## Exact interpretations -/

section Exact

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
  [Monad m] [Assertion Pred] [Assertion EPred] [LE Pred] [LE EPred]
  [LERelCompat Pred] [LERelCompat EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred]

/-- The observation of an exact `WPMonad` as an `XCoreWP` at grade type `Unit` is lawful. -/
theorem lawfulXCoreWP_ofExactWPMonad :
    @LawfulXCoreWP m Pred EPred Unit _ _ _ _ (XCoreWP.ofWPMonad m) :=
  lawfulXCoreWP_ofWPMonad (fun a post epost => ExactWPMonad.wp_pure a post epost)
    (fun c f post epost => ExactWPMonad.wp_bind c f post epost)

end Exact

/-! ## Agreement of `≤` with `⊑` on Mathlib complete lattices -/

/-- On a Mathlib complete lattice with PolyFun's order bridge, `≤` is `⊑`. -/
instance instLERelCompatOfCompleteLattice {l : Type u} [CompleteLattice l] :
    LERelCompat l :=
  ⟨fun _ _ => Iff.rfl⟩

/-- On the empty exception postcondition `EStack⟨⟩` both orders are total. -/
instance instLERelCompatUnit : LERelCompat EStack⟨⟩ :=
  ⟨fun a b => iff_of_true (le_of_eq (Subsingleton.elim a b))
    (Lean.Order.PartialOrder.rel_of_eq (Subsingleton.elim a b))⟩

/-! ## Ordered monad algebras -/

section MAlg

variable (m : Type u → Type v) (l : Type u) [Monad m] [LawfulMonad m] [CompleteLattice l]
  [MAlgOrdered m l]

/-- The observation of the interpretation `MAlgOrdered.toWPMonad` of an ordered monad
algebra, at grade type `Unit`. -/
@[reducible] def XCoreWP.ofMAlgOrdered : XCoreWP m l EStack⟨⟩ Unit :=
  @XCoreWP.ofWPMonad m l EStack⟨⟩ _ _ _ _ _ _ _ MAlgOrdered.toWPMonad

/-- The observation of an ordered monad algebra is lawful. -/
theorem lawfulXCoreWP_ofMAlgOrdered :
    @LawfulXCoreWP m l EStack⟨⟩ Unit _ _ _ _ (XCoreWP.ofMAlgOrdered m l) :=
  letI := MAlgOrdered.toWPMonad (m := m) (l := l)
  lawfulXCoreWP_ofExactWPMonad

variable {m l}

/-- The weakest precondition of the observation of an ordered monad algebra is the
algebra of the program with its outputs mapped through the postcondition (the unfolding
lemma of `XCoreWP.ofMAlgOrdered`). -/
theorem ofMAlgOrdered_wp {α : Type u} (x : m α) (post : α → l) (epost : EStack⟨⟩) :
    (@XCoreWP.wp m l EStack⟨⟩ Unit _ _ (XCoreWP.ofMAlgOrdered m l) α x).apply post epost =
      MAlgOrdered.μ (x >>= fun a => pure (post a)) :=
  rfl

/-- A triple of the observation of an ordered monad algebra is a lower bound of the
algebra of the mapped program (the unfolding of `XCoreWP.Triple` at
`XCoreWP.ofMAlgOrdered`). -/
theorem ofMAlgOrdered_triple_iff {α : Type u} (x : m α) (pre : l) (post : α → l)
    (epost : EStack⟨⟩) :
    @XCoreWP.Triple m l EStack⟨⟩ Unit _ _ (XCoreWP.ofMAlgOrdered m l) α pre x post epost ↔
      pre ≤ MAlgOrdered.μ (x >>= fun a => pure (post a)) :=
  Iff.rfl

end MAlg

/-! ## Free programs under a per-operation specification -/

section OpSpec

variable {P : PFunctor.{uA, uB}} {l : Type uB} [CompleteLattice l]

/-- The observation of the interpretation `OpSpec.toWPMonad` of free programs under a
monotone per-operation specification, at grade type `Unit`. -/
@[reducible] def XCoreWP.ofOpSpec (Φ : PFunctor.OpSpec P l) (hΦ : Φ.Monotone) :
    XCoreWP (PFunctor.FreeM P) l EStack⟨⟩ Unit :=
  @XCoreWP.ofWPMonad (PFunctor.FreeM P) l EStack⟨⟩ _ _ _ _ _ _ _ (Φ.toWPMonad hΦ)

/-- The observation of free programs under a monotone per-operation specification is
lawful. -/
theorem lawfulXCoreWP_ofOpSpec (Φ : PFunctor.OpSpec P l) (hΦ : Φ.Monotone) :
    @LawfulXCoreWP (PFunctor.FreeM P) l EStack⟨⟩ Unit _ _ _ _ (XCoreWP.ofOpSpec Φ hΦ) :=
  letI := Φ.toWPMonad hΦ
  lawfulXCoreWP_ofExactWPMonad

/-- The weakest precondition of the observation of free programs under a monotone
per-operation specification is the fold `FreeM.wpFold`. -/
theorem ofOpSpec_wp (Φ : PFunctor.OpSpec P l) (hΦ : Φ.Monotone) {α : Type uB}
    (x : PFunctor.FreeM P α) (post : α → l) (epost : EStack⟨⟩) :
    (@XCoreWP.wp (PFunctor.FreeM P) l EStack⟨⟩ Unit _ _ (XCoreWP.ofOpSpec Φ hΦ) α x).apply
        post epost =
      PFunctor.FreeM.wpFold Φ x post :=
  PFunctor.OpSpec.toWPMonad_wp Φ hΦ x post epost

end OpSpec

end CatCrypt.Crypto.VCVioBridge.XDijkstra
