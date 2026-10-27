/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPullback
public import PolyFun.Control.Monad.Hom
public import PolyFun.PFunctor.Free.Basic

/-!
# XDijkstra observations along PolyFun monad homomorphisms

A PolyFun monad homomorphism `F : m →ᵐ n` is a monad morphism in the sense of
`IsMonadMorphism`, so an XDijkstra observation of `n` pulls back to a lawful
observation of `m` (`XCoreWP.pullback`). The fold `FreeM.liftM s` of a handler
`s : (a : P.A) → n (P.B a)` is such a homomorphism (`FreeM.liftMHom`): free-monad
syntax over `P` is observed through its interpretation, its triples are the triples of
the interpreted program, and a generator `FreeM.lift a` has the triples of `s a`.

PolyFun's `MonadHom.transportWP` pulls back a `Std.WP` interpretation along the same
morphism with the same transformer, `wp (F x)`; the two constructions agree on
weakest preconditions by definition.

## Main results

* `isMonadMorphism_monadHom`: a PolyFun monad homomorphism preserves `pure` and `bind`.
* `lawful_pullback_monadHom`: the observation pulled back along a homomorphism is
  lawful.
* `lawful_pullback_freeM`: the observation of free-monad syntax through a handler is
  lawful.
* `freeM_lift_triple_iff`: a generator has the triples of its handler.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.VCVioBridge.XDijkstra

open CatCrypt.XDijkstra

universe u v w x y g uA uB

section MonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  {Pred : Type x} {EPred : Type y} {G : Type g} [LE Pred] [LE EPred]

/-- A PolyFun monad homomorphism preserves `pure` and `bind`. -/
theorem isMonadMorphism_monadHom (F : m →ᵐ n) : IsMonadMorphism m n (fun x => F x) :=
  ⟨F.mmap_pure, F.mmap_bind⟩

/-- The observation of `m` pulled back along a PolyFun monad homomorphism is lawful when
the observation of `n` is lawful. -/
theorem lawful_pullback_monadHom [Zero G] [XCoreWP n Pred EPred G]
    [LawfulXCoreWP n Pred EPred] (F : m →ᵐ n) :
    @LawfulXCoreWP m Pred EPred G _ _ _ _ (XCoreWP.pullback fun x => F x) :=
  XCoreWP.lawful_pullback (isMonadMorphism_monadHom F)

end MonadHom

section FreeM

variable {P : PFunctor.{uA, uB}} {n : Type uB → Type v} [Monad n] [LawfulMonad n]
  {Pred : Type x} {EPred : Type y} {G : Type g} [LE Pred] [LE EPred]

/-- The observation of free-monad syntax over `P` through a handler `s` into an
observed monad is lawful when the observation of the target is lawful. -/
theorem lawful_pullback_freeM [Zero G] [XCoreWP n Pred EPred G]
    [LawfulXCoreWP n Pred EPred] (s : (a : P.A) → n (P.B a)) :
    @LawfulXCoreWP P.FreeM Pred EPred G _ _ _ _
      (XCoreWP.pullback fun x => PFunctor.FreeM.liftM s x) :=
  lawful_pullback_monadHom (PFunctor.FreeM.liftMHom s)

/-- Under the observation through a handler `s`, the generator `FreeM.lift a` has the
triples of `s a`. -/
theorem freeM_lift_triple_iff [XCoreWP n Pred EPred G] (s : (a : P.A) → n (P.B a))
    (a : P.A) (Pre : Pred) (post : P.B a → Pred) (epost : EPred) :
    @XCoreWP.Triple P.FreeM Pred EPred G _ _
        (XCoreWP.pullback fun x => PFunctor.FreeM.liftM s x) _ Pre (PFunctor.FreeM.lift a)
        post epost
      ↔ XCoreWP.Triple (m := n) Pre (s a) post epost := by
  rw [XCoreWP.pullback_triple_iff, PFunctor.FreeM.liftM_lift]

end FreeM

end CatCrypt.Crypto.VCVioBridge.XDijkstra
