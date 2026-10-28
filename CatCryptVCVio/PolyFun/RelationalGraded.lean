/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.Rel.XRelSpecMonad
public import PolyFun.Control.Monad.Algebra.Relational

/-!
# Graded relational monad algebras

`MAlgRelGraded G m₁ m₂ l` is a relational weakest precondition `grwp g x y post : l`
indexed by a grade `g` of an additive monoid `G` with a preorder: pure at grade `0` as an
equation, monotone in the postcondition and in the grade, and bind at the sum of the
grades. It is the graded form of PolyFun's `MAlgRelOrdered`, in the sense of the graded
Hoare logic of Gaboardi, Katsumata, Orchard and Sato (ESOP 2021) for the fibration of
`l`-valued binary relations: the two monads are ungraded and the grade indexes the
relational observation.

The grade-`0` restriction of a graded algebra is an `MAlgRelOrdered` (`atZero`), and every
`MAlgRelOrdered` is a graded algebra constant in the grade (`ofMAlgRelOrdered`). For a
relational Q₀-monad `T` whose monad structure is the one of its lifting
(`RelQ0MonadCompat`), approximate couplings form a graded algebra over `Prop` at grades in
`ℝ≥0∞`: `grwp ε x y post` is `RelQ0.liftR ε post x y`.

## Main results

* `MAlgRelGraded`, its triple `MAlgRelGraded.GTriple` and the graded triple rules.
* `MAlgRelGraded.atZero`, `MAlgRelGraded.ofMAlgRelOrdered`,
  `MAlgRelGraded.atZero_ofMAlgRelOrdered` and `MAlgRelGraded.unitEquiv`.
* `liftRApprox_pure_inv_of_lt_one`, `RelQ0.liftR_pure_inv_of_lt_one`: a sub-coupling of two
  point masses at an error below `1` relates the two points.
* `RelQ0MonadCompat`: the monad structure of `T` is the one of its lifting; `SDistr` is an
  instance.
* `instMAlgRelGradedRelQ0`: approximate couplings form an `MAlgRelGraded ℝ≥0∞ T T Prop`.
* `grwp_adequate`: a graded relational precondition gives a sub-coupling of the
  denotations at its grade.
-/

@[expose] public section
set_option autoImplicit false

universe u v₁ v₂ w

namespace CatCrypt.Crypto.VCVioBridge.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob CatCrypt.Relational

/-- **Graded ordered relational monad algebra** between two monads: a relational weakest
precondition indexed by a grade, pure at grade `0`, monotone in the postcondition and in
the grade, and bind at the sum of the grades. -/
class MAlgRelGraded (G : Type w) [AddMonoid G] [Preorder G]
    (m₁ : Type u → Type v₁) (m₂ : Type u → Type v₂) (l : Type u)
    [Monad m₁] [Monad m₂] [Preorder l] where
  /-- Graded relational weakest precondition. -/
  grwp : {α β : Type u} → G → m₁ α → m₂ β → (α → β → l) → l
  /-- Pure rule at grade `0`. -/
  grwp_pure {α β : Type u} (a : α) (b : β) (post : α → β → l) :
      grwp (0 : G) (pure a) (pure b) post = post a b
  /-- Monotonicity in the relational postcondition. -/
  grwp_mono {α β : Type u} {g : G} {x : m₁ α} {y : m₂ β} {post post' : α → β → l}
      (hpost : ∀ a b, post a b ≤ post' a b) :
      grwp g x y post ≤ grwp g x y post'
  /-- Monotonicity in the grade. -/
  grwp_mono_grade {α β : Type u} {g g' : G} (x : m₁ α) (y : m₂ β) (post : α → β → l)
      (hg : g ≤ g') : grwp g x y post ≤ grwp g' x y post
  /-- Sequential composition at the sum of the grades. -/
  grwp_bind_le {α β γ δ : Type u} (g h : G) (x : m₁ α) (y : m₂ β)
      (f : α → m₁ γ) (k : β → m₂ δ) (post : γ → δ → l) :
      grwp g x y (fun a b => grwp h (f a) (k b) post) ≤ grwp (g + h) (x >>= f) (y >>= k) post

namespace MAlgRelGraded

variable {G : Type w} [AddMonoid G] [Preorder G]
  {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
  [Monad m₁] [Monad m₂] [Preorder l]

section Rules

variable [MAlgRelGraded G m₁ m₂ l] {α β γ δ : Type u}

/-- Graded relational triple: `pre` is below the graded relational weakest precondition at
grade `g`. -/
def GTriple (g : G) (pre : l) (x : m₁ α) (y : m₂ β) (post : α → β → l) : Prop :=
  pre ≤ grwp g x y post

/-- Pure rule at grade `0`. -/
theorem gtriple_pure {pre : l} {a : α} {b : β} {post : α → β → l}
    (hpre : pre ≤ post a b) :
    GTriple (0 : G) pre (pure a : m₁ α) (pure b : m₂ β) post := by
  rw [GTriple, grwp_pure]
  exact hpre

/-- Pure rule at every grade above `0`. -/
theorem gtriple_pure_of_nonneg {g : G} (hg : 0 ≤ g) {pre : l} {a : α} {b : β}
    {post : α → β → l} (hpre : pre ≤ post a b) :
    GTriple g pre (pure a : m₁ α) (pure b : m₂ β) post :=
  le_trans (gtriple_pure (G := G) (m₁ := m₁) (m₂ := m₂) hpre) (grwp_mono_grade _ _ _ hg)

/-- Consequence rule: strengthen the precondition, weaken the postcondition and raise the
grade. -/
theorem gtriple_conseq {g g' : G} {pre pre' : l} {x : m₁ α} {y : m₂ β}
    {post post' : α → β → l} (hg : g ≤ g') (hpre : pre' ≤ pre)
    (hpost : ∀ a b, post a b ≤ post' a b) :
    GTriple g pre x y post → GTriple g' pre' x y post' := by
  intro h
  exact le_trans hpre (le_trans h (le_trans (grwp_mono hpost) (grwp_mono_grade x y _ hg)))

/-- Monotonicity of the triple in the grade. -/
theorem gtriple_mono_grade {g g' : G} {pre : l} {x : m₁ α} {y : m₂ β}
    {post : α → β → l} (hg : g ≤ g') (h : GTriple g pre x y post) :
    GTriple g' pre x y post :=
  gtriple_conseq hg le_rfl (fun _ _ => le_rfl) h

/-- Bind rule: the grades of the two steps add. -/
theorem gtriple_bind {g h : G} {pre : l} {x : m₁ α} {y : m₂ β}
    {f : α → m₁ γ} {k : β → m₂ δ} {cut : α → β → l} {post : γ → δ → l}
    (hxy : GTriple g pre x y cut) (hfk : ∀ a b, GTriple h (cut a b) (f a) (k b) post) :
    GTriple (g + h) pre (x >>= f) (y >>= k) post :=
  le_trans hxy (le_trans (grwp_mono hfk) (grwp_bind_le g h x y f k post))

/-- Bind rule at a stated budget `e` above the sum of the grades. -/
theorem gtriple_bind_le {g h e : G} (he : g + h ≤ e) {pre : l} {x : m₁ α} {y : m₂ β}
    {f : α → m₁ γ} {k : β → m₂ δ} {cut : α → β → l} {post : γ → δ → l}
    (hxy : GTriple g pre x y cut) (hfk : ∀ a b, GTriple h (cut a b) (f a) (k b) post) :
    GTriple e pre (x >>= f) (y >>= k) post :=
  gtriple_mono_grade he (gtriple_bind hxy hfk)

/-- Mapping on the left program is monotone for the graded relational WP. -/
theorem grwp_map_left [LawfulMonad m₁] [LawfulMonad m₂] (g : G)
    (f : α → γ) (x : m₁ α) (y : m₂ β) (post : γ → β → l) :
    grwp g x y (fun a b => post (f a) b) ≤ grwp g (f <$> x) y post := by
  have hbind := grwp_bind_le g 0 x y (fun a => pure (f a)) (fun b => (pure b : m₂ β)) post
  simpa only [grwp_pure, add_zero, bind_pure, bind_pure_comp] using hbind

/-- Mapping on the right program is monotone for the graded relational WP. -/
theorem grwp_map_right [LawfulMonad m₁] [LawfulMonad m₂] (g : G)
    (k : β → δ) (x : m₁ α) (y : m₂ β) (post : α → δ → l) :
    grwp g x y (fun a b => post a (k b)) ≤ grwp g x (k <$> y) post := by
  have hbind := grwp_bind_le g 0 x y (fun a => (pure a : m₁ α)) (fun b => pure (k b)) post
  simpa only [grwp_pure, add_zero, bind_pure, bind_pure_comp] using hbind

/-- Asynchronous bind on the left: the right side performs no bind step. -/
theorem grwp_bind_left_le [LawfulMonad m₂] (g h : G)
    (x : m₁ α) (f : α → m₁ γ) (y : m₂ β) (post : γ → β → l) :
    grwp g x y (fun a b => grwp h (f a) (pure b : m₂ β) post) ≤
      grwp (g + h) (x >>= f) y post := by
  have hb := grwp_bind_le g h x y f (fun b : β => (pure b : m₂ β)) post
  simpa only [bind_pure] using hb

/-- Asynchronous bind on the right: the left side performs no bind step. -/
theorem grwp_bind_right_le [LawfulMonad m₁] (g h : G)
    (x : m₁ α) (y : m₂ β) (k : β → m₂ δ) (post : α → δ → l) :
    grwp g x y (fun a b => grwp h (pure a : m₁ α) (k b) post) ≤
      grwp (g + h) x (y >>= k) post := by
  have hb := grwp_bind_le g h x y (fun a : α => (pure a : m₁ α)) k post
  simpa only [bind_pure] using hb

end Rules

/-- The grade-`0` restriction of a graded relational monad algebra is a PolyFun relational
monad algebra. -/
@[instance_reducible]
def atZero (G : Type w) [AddMonoid G] [Preorder G] [MAlgRelGraded G m₁ m₂ l] :
    MAlgRelOrdered m₁ m₂ l where
  rwp x y post := grwp (0 : G) x y post
  rwp_pure := grwp_pure (G := G)
  rwp_mono h := grwp_mono (G := G) h
  rwp_bind_le x y f k post := by
    have hb := grwp_bind_le (G := G) 0 0 x y f k post
    rwa [add_zero] at hb

/-- A PolyFun relational monad algebra is a graded relational monad algebra constant in the
grade. -/
@[instance_reducible]
def ofMAlgRelOrdered (G : Type w) [AddMonoid G] [Preorder G] (I : MAlgRelOrdered m₁ m₂ l) :
    MAlgRelGraded G m₁ m₂ l where
  grwp _ x y post := I.rwp x y post
  grwp_pure := I.rwp_pure
  grwp_mono h := I.rwp_mono h
  grwp_mono_grade _ _ _ _ := le_rfl
  grwp_bind_le _ _ x y f k post := I.rwp_bind_le x y f k post

/-- The grade-`0` restriction of the graded algebra constant in the grade is the original
algebra. -/
theorem atZero_ofMAlgRelOrdered (G : Type w) [AddMonoid G] [Preorder G]
    (I : MAlgRelOrdered m₁ m₂ l) :
    (letI := ofMAlgRelOrdered G I; atZero G) = I := by
  cases I
  rfl

/-- At the trivial grade monoid `Unit`, graded relational monad algebras are PolyFun's
relational monad algebras. -/
def unitEquiv : MAlgRelGraded Unit m₁ m₂ l ≃ MAlgRelOrdered m₁ m₂ l where
  toFun J := atZero Unit
  invFun := ofMAlgRelOrdered Unit
  left_inv J := by
    cases J
    congr 1
  right_inv := atZero_ofMAlgRelOrdered Unit

end MAlgRelGraded

/-- An approximate sub-coupling of two point masses at an error below `1` relates the two
points. -/
theorem liftRApprox_pure_inv_of_lt_one {α β : Type} {ε : ℝ≥0∞} {R : α → β → Prop}
    {a : α} {b : β} (hε : ε < 1) (h : liftRApprox ε R (SDistr.pure a) (SDistr.pure b)) :
    R a b := by
  classical
  obtain ⟨c, hc⟩ := h
  by_contra hn
  have hz : ∀ a' b', c.joint (some (a', b')) = 0 := by
    intro a' b'
    by_contra hne
    have ha : a' = a := by
      by_contra hx
      have h1 := c.left_le a'
      have h2 : c.joint (some (a', b')) ≤ ∑' b'', c.joint (some (a', b'')) :=
        ENNReal.le_tsum (f := fun b'' => c.joint (some (a', b''))) b'
      simp [SDistr.pure_apply_some, Ne.symm hx] at h1
      grind
    have hb : b' = b := by
      by_contra hx
      have h1 := c.right_le b'
      have h2 : c.joint (some (a', b')) ≤ ∑' a'', c.joint (some (a'', b')) :=
        ENNReal.le_tsum (f := fun a'' => c.joint (some (a'', b'))) a'
      simp [SDistr.pure_apply_some, Ne.symm hx] at h1
      grind
    subst ha hb
    exact hn (hc _ _ hne)
  have hdef := c.left_deficit
  simp only [hz, tsum_zero, tsub_zero] at hdef
  have h1 : (∑' a', (SDistr.pure a : SDistr α) (some a')) = 1 :=
    SDistr.tsum_some_eq_one_of_none_zero (SDistr.pure_apply_none _)
  rw [h1] at hdef
  exact absurd (lt_of_le_of_lt hdef hε) (lt_irrefl _)

/-- In every `RelQ0`, a lifting of a relation to two point masses at an error below `1`
relates the two points. -/
theorem RelQ0.liftR_pure_inv_of_lt_one {T : Type → Type} [RelQ0 T] {α β : Type}
    {ε : ℝ≥0∞} {R : α → β → Prop} {a : α} {b : β} (hε : ε < 1)
    (h : RelQ0.liftR ε R (RelQ0.pure' (T := T) a) (RelQ0.pure' (T := T) b)) : R a b := by
  have hA := RelQ0.liftR_adequate h CatCrypt.Core.Heap.empty
  rw [RelQ0.denote_pure, RelQ0.denote_pure] at hA
  exact (liftRApprox_pure_inv_of_lt_one hε hA).1

/-- The monad structure of `T` is the one of its graded relational lifting: `pure` is
`RelQ0.pure'` and `bind` is `RelQ0.bind'`. -/
class RelQ0MonadCompat (T : Type → Type) [Monad T] [RelQ0Lift T] : Prop where
  /-- `pure` is the unit of the lifting. -/
  pure_eq : ∀ {α : Type} (a : α), (pure a : T α) = RelQ0.pure' a
  /-- `bind` is the bind of the lifting. -/
  bind_eq : ∀ {α β : Type} (x : T α) (f : α → T β), x >>= f = RelQ0.bind' x f

/-- The monad structure of `SDistr` is the one of its sub-coupling lifting. -/
instance : RelQ0MonadCompat SDistr where
  pure_eq _ := rfl
  bind_eq _ _ := rfl

/-- **Approximate couplings as a graded relational monad algebra.** The graded relational
weakest precondition of `x` and `y` at `post` and grade `ε` is the `ε`-approximate coupling
`RelQ0.liftR ε post x y`. The pure law at grade `0` holds as an equation of propositions by
`propext`, from `RelQ0.liftR_pure` and its converse `RelQ0.liftR_pure_inv_of_lt_one`; the
bind law is `RelQ0.liftR_bind`. -/
instance instMAlgRelGradedRelQ0 {T : Type → Type} [Monad T] [RelQ0 T] [RelQ0MonadCompat T] :
    MAlgRelGraded ℝ≥0∞ T T Prop where
  grwp ε x y post := RelQ0.liftR ε post x y
  grwp_pure a b post := by
    rw [RelQ0MonadCompat.pure_eq, RelQ0MonadCompat.pure_eq]
    exact propext ⟨RelQ0.liftR_pure_inv_of_lt_one zero_lt_one, RelQ0.liftR_pure⟩
  grwp_mono hpost := RelQ0.liftR_mono_rel hpost
  grwp_mono_grade _ _ _ hg := RelQ0.liftR_mono_eps hg
  grwp_bind_le _ _ x y f k post := by
    intro h
    rw [RelQ0MonadCompat.bind_eq, RelQ0MonadCompat.bind_eq]
    exact RelQ0.liftR_bind h (fun _ _ hab => hab)

/-- **Adequacy of the graded coupling algebra.** From `grwp ε x y post` and every initial
heap, the denotations of `x` and `y` have an `ε`-approximate sub-coupling supported on
pairs whose values are related by `post` and whose final heaps are equal. -/
theorem grwp_adequate {T : Type → Type} [Monad T] [RelQ0 T] [RelQ0MonadCompat T]
    {α β : Type} {ε : ℝ≥0∞} {x : T α} {y : T β} {post : α → β → Prop}
    (h : MAlgRelGraded.grwp ε x y post) (hp : CatCrypt.Core.Heap) :
    liftRApprox ε (fun p q => post p.1 q.1 ∧ p.2 = q.2)
      (RelQ0.denote x hp) (RelQ0.denote y hp) :=
  RelQ0.liftR_adequate h hp

end CatCrypt.Crypto.VCVioBridge.XDijkstra
