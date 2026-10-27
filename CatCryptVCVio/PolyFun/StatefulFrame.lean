/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import PolyFun.PFunctor.Handler.Stateful.Combinators
public import CatCryptCore.XDijkstra.XFrameHet
public import CatCryptCore.XDijkstra.XStdWP

/-!
# The frame rule of PolyFun's sum of stateful handlers

A stateful handler `h : Handler.Stateful m S P` interprets a free program `x : FreeM P α` as
the stateful program `x.liftM h : StateT S m α`. For a base monad `m` with a `Std.WP`
interpretation `WPMonad m Prop EPred`, the toolchain lifts it to `StateT S m` with
assertions `S → Prop`, and `XCoreWP.ofWPMonad` observes the stateful program by an
XDijkstra transformer `runPT h x`. The sum `Stateful.sum f g` runs `f` and `g` on the two
summands of `P + Q` with product state `S × T`. A program over `P`, relabelled along
`Lens.inl`, changes only the first state component: its observation under `sum f g` is
local along the product separation `A s ∧ F t`, with respect to the observation of the
program under `f`, and `XCorePT.frameAlong` gives the frame rule
`{A} f {B} ⟹ {A ⊗ F} sum f g ∘ inl {B ⊗ F}`, and symmetrically for the right summand.

Both results are instances of locality along a state embedding: for a family
`emb t : S → S'` commuting with every request of `h` and `h'`
(`run_map_eq_of_apply_map_eq`), the observations of `h` and `h'` are local along every
separation whose assertions hold exactly on the image of `emb` at the frame. The proof
uses only the lower laws of `WPMonad` (`WPMonad.map_le_wp_map`) and monotonicity.

## Main results

* `runPT_localAlong_of_embed`: locality along a state embedding commuting with requests.
* `runPT_sum_inl_localAlong`, `runPT_sum_inr_localAlong`: locality of a relabelled program
  under the sum of stateful handlers along the product separation.
* `runPT_sum_inl_frame`, `runPT_sum_inr_frame`: the frame rules of the sum.
* `triple_sum_inl_frame`, `triple_sum_inr_frame`: the same frame rules for `Std.WP` triples.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.VCVioBridge.XDijkstra

open CatCrypt.XDijkstra CatCrypt.StdWPBridge Std.WP
open PFunctor PFunctor.Handler

universe u v w uA uA'

variable {m : Type u → Type v} {EPred : Type w} [Monad m] [Assertion EPred]
  [LE EPred] [LERelCompat EPred] [WPMonad m Prop EPred]
  {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}} {α : Type u}

/-- The XDijkstra observation of a free program run through a stateful handler: the
weakest precondition of `x.liftM h : StateT S m α` under the lifted `WPMonad`. -/
noncomputable def runPT {S : Type u} (h : Stateful m S P) (x : FreeM P α) :
    XCorePT (S → Prop) EPred Unit α :=
  @XCoreWP.wp (StateT S m) (S → Prop) EPred Unit _ _ (XCoreWP.ofWPMonad (StateT S m)) α
    (x.liftM h)

/-- Unfolding lemma of `runPT`: the weakest precondition of `runPT h x` at a state is the
weakest precondition of the run from that state. -/
theorem runPT_apply {S : Type u} (h : Stateful m S P) (x : FreeM P α) (post : α → S → Prop)
    (epost : EPred) (s : S) :
    (runPT h x).apply post epost s = wp (h.run x s) (fun r => post r.1 r.2) epost := rfl

/-- **Locality along a state embedding.** For a family of state maps `emb t : S → S'`, each
commuting with every request of `h` and `h'`, and a separation `sep A F` that holds at
`s'` exactly when `s'` is `emb t s` with `A s` and `F t`, the observations of `h` and `h'`
on the same program are local along `sep`. -/
theorem runPT_localAlong_of_embed {S S' : Type u} {T : Type*} (h : Stateful m S P)
    (h' : Stateful m S' P) (emb : T → S → S')
    (hemb : ∀ t a s, Prod.map _root_.id (emb t) <$> (h a).run s = (h' a).run (emb t s))
    (sep : (S → Prop) → (T → Prop) → S' → Prop)
    (hsep_elim : ∀ A F s', sep A F s' → ∃ s t, s' = emb t s ∧ A s ∧ F t)
    (hsep_intro : ∀ A F s t, A s → F t → sep A F (emb t s)) (x : FreeM P α) :
    XCorePT.LocalAlong sep (fun _ => True) (runPT h x) (runPT h' x) := by
  intro post _ epost R s' hs'
  obtain ⟨s, t, rfl, hA, hR⟩ := hsep_elim _ _ _ hs'
  rw [runPT_apply] at hA ⊢
  rw [← Stateful.run_map_eq_of_apply_map_eq h h' (emb t) (hemb t) x s]
  have hc := (LERelCompat.le_iff_rel _ _).2
    (WP.wp_consequence (h.run x s) (fun r => post r.1 r.2)
      (fun r => sep (post r.1) R (emb t r.2)) epost (fun r hr => hsep_intro _ _ _ _ hr hR)) hA
  exact (LERelCompat.le_iff_rel _ _).2 (WPMonad.map_le_wp_map (Prod.map _root_.id (emb t))
    (h.run x s) (fun r => sep (post r.1) R r.2) epost) hc

/-! ## The sum of stateful handlers -/

section Sum

variable {S T : Type u}

/-- The product separation with the frame on the second component: `A` holds of the first
component and the spectator `F` of the second. -/
def sepFst (A : S → Prop) (F : T → Prop) : S × T → Prop := fun st => A st.1 ∧ F st.2

/-- The product separation with the frame on the first component: `A` holds of the second
component and the spectator `F` of the first. -/
def sepSnd (A : S → Prop) (F : T → Prop) : T × S → Prop := fun st => F st.1 ∧ A st.2

/-- A program relabelled along `Lens.inl` and run through `sum f g` is observed as the
original program run through the left requests of `sum f g`. -/
theorem runPT_sum_mapLens_inl (f : Stateful m S P) (g : Stateful m T Q) (x : FreeM P α) :
    runPT (Stateful.sum f g) (x.mapLens Lens.inl) =
      runPT (fun a => Stateful.sum f g (.inl a)) x := by
  unfold runPT
  rw [Handler.liftM_mapLens_inl_eq_of_apply _ _ (fun _ => rfl) x]

/-- A program relabelled along `Lens.inr` and run through `sum f g` is observed as the
original program run through the right requests of `sum f g`. -/
theorem runPT_sum_mapLens_inr (f : Stateful m S P) (g : Stateful m T Q) (x : FreeM Q α) :
    runPT (Stateful.sum f g) (x.mapLens Lens.inr) =
      runPT (fun b => Stateful.sum f g (.inr b)) x := by
  unfold runPT
  rw [Handler.liftM_mapLens_inr_eq_of_apply _ _ (fun _ => rfl) x]

/-- **Locality of the left summand.** A program over `P`, relabelled into `P + Q` and run
through `sum f g`, is local along `sepFst` with respect to the program run through `f`. -/
theorem runPT_sum_inl_localAlong (f : Stateful m S P) (g : Stateful m T Q) (x : FreeM P α) :
    XCorePT.LocalAlong sepFst (fun _ => True) (runPT f x)
      (runPT (Stateful.sum f g) (x.mapLens Lens.inl)) := by
  rw [runPT_sum_mapLens_inl]
  exact runPT_localAlong_of_embed f _ (fun t s => (s, t)) (fun _ _ _ => rfl) sepFst
    (fun _ _ st hst => ⟨st.1, st.2, rfl, hst⟩) (fun _ _ _ _ hA hF => ⟨hA, hF⟩) x

/-- **Locality of the right summand.** A program over `Q`, relabelled into `P + Q` and run
through `sum f g`, is local along `sepSnd` with respect to the program run through `g`. -/
theorem runPT_sum_inr_localAlong (f : Stateful m S P) (g : Stateful m T Q) (x : FreeM Q α) :
    XCorePT.LocalAlong sepSnd (fun _ => True) (runPT g x)
      (runPT (Stateful.sum f g) (x.mapLens Lens.inr)) := by
  rw [runPT_sum_mapLens_inr]
  exact runPT_localAlong_of_embed g _ (fun s t => (s, t)) (fun _ _ _ => rfl) sepSnd
    (fun _ _ st hst => ⟨st.2, st.1, rfl, hst.2, hst.1⟩) (fun _ _ _ _ hA hF => ⟨hF, hA⟩) x

/-- **The frame rule of the left summand.** From `{A} f.run x {B}` conclude
`{A ⊗ F} (sum f g).run (inl x) {B ⊗ F}` for every spectator `F` on the second state
component. -/
theorem runPT_sum_inl_frame (f : Stateful m S P) (g : Stateful m T Q) {x : FreeM P α}
    {A : S → Prop} {B : α → S → Prop} {epost : EPred} (F : T → Prop)
    (h : XCorePT.Triple A (runPT f x) B epost) :
    XCorePT.Triple (sepFst A F) (runPT (Stateful.sum f g) (x.mapLens Lens.inl))
      (fun a => sepFst (B a) F) epost :=
  XCorePT.frameAlong (fun _ hab _ hst => ⟨hab _ hst.1, hst.2⟩)
    (runPT_sum_inl_localAlong f g x) trivial F h

/-- **The frame rule of the right summand.** From `{A} g.run x {B}` conclude
`{F ⊗ A} (sum f g).run (inr x) {F ⊗ B}` for every spectator `F` on the first state
component. -/
theorem runPT_sum_inr_frame (f : Stateful m S P) (g : Stateful m T Q) {x : FreeM Q α}
    {A : T → Prop} {B : α → T → Prop} {epost : EPred} (F : S → Prop)
    (h : XCorePT.Triple A (runPT g x) B epost) :
    XCorePT.Triple (sepSnd A F) (runPT (Stateful.sum f g) (x.mapLens Lens.inr))
      (fun a => sepSnd (B a) F) epost :=
  XCorePT.frameAlong (fun _ hab _ hst => ⟨hst.1, hab _ hst.2⟩)
    (runPT_sum_inr_localAlong f g x) trivial F h

/-- The frame rule of the left summand for `Std.WP` triples of the stateful programs. -/
theorem triple_sum_inl_frame (f : Stateful m S P) (g : Stateful m T Q) {x : FreeM P α}
    {A : S → Prop} {B : α → S → Prop} {epost : EPred} (F : T → Prop)
    (h : Triple (x.liftM f) A B epost) :
    Triple ((x.mapLens Lens.inl).liftM (Stateful.sum f g)) (sepFst A F)
      (fun a => sepFst (B a) F) epost :=
  triple_iff_xcoreTriple.2 (runPT_sum_inl_frame f g F (triple_iff_xcoreTriple.1 h))

/-- The frame rule of the right summand for `Std.WP` triples of the stateful programs. -/
theorem triple_sum_inr_frame (f : Stateful m S P) (g : Stateful m T Q) {x : FreeM Q α}
    {A : T → Prop} {B : α → T → Prop} {epost : EPred} (F : S → Prop)
    (h : Triple (x.liftM g) A B epost) :
    Triple ((x.mapLens Lens.inr).liftM (Stateful.sum f g)) (sepSnd A F)
      (fun a => sepSnd (B a) F) epost :=
  triple_iff_xcoreTriple.2 (runPT_sum_inr_frame f g F (triple_iff_xcoreTriple.1 h))

end Sum

end CatCrypt.Crypto.VCVioBridge.XDijkstra
