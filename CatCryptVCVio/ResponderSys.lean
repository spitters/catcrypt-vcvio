/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Relational
public import CatCryptCore.Crypto.UCTransparent
public import VCVio.OracleComp.Coinductive.Responder

/-!
# Stateful responders as reactive systems

VCVio's probabilistic stateful responder `ProbResponder spec` answers each query `t` from a
state with a joint distribution over an answer in `spec.Range t` and a successor state; an
`OracleStrategy S spec` asks the next query from its state and digests the answer. CatCrypt's
reactive system `UCTransparent.Sys τ E O` has a step `τ → E → SPComp (τ × O)`, run against an
environment `UCTransparent.Strat ζ E O` by `UCTransparent.loop` / `run` / `view`.

The events of the translated system are the queries `spec.Domain`. The outputs are the tagged
answers `Answer spec = Σ t, spec.Range t`: `Sys` has one output type for every event, and the
tag records which query an output answers. A system produced by `toSys` always tags an output
with the query it answers; the environment `toStrat` reads an answer to its own exposed query
through `ResponderSys.absorb`.

## Main definitions

* `toSys R r₀` — an executable responder as a reactive system, its step the lift
  `probCompLift` of the executable answer program
* `toStrat A s₀ n` — an oracle strategy as an environment running `n` activations
* `ofSys S h` — a reactive system with tagged outputs, at a fixed heap `h`, as a kernel
  responder on the discrete state space; a mistagged output is failure mass

## Main results

* `loop_toSys` / `run_toSys` / `view_toSys` — the joint run of `toStrat A` against `toSys R` is
  the lift of VCVio's wired run `OracleStrategy.iterateAgainst A R`
* `adv_toSys` — the advantage of an environment built from a strategy and a `ProbComp`
  distinguisher between two translated responders is the gap of VCVio's output masses
* `gap_iterateAgainst_le_of_realizes` — a realization bound between two translated responders
  bounds the VCVio-side distinguishing gap of every strategy
* `ofSys_toSys_answerKernel` — translating a stateful handler to a system and back gives the
  kernel of the handler's responder

Only executable responders translate to systems: a kernel responder over an abstract measurable
state space has no `SPComp` program. In the other direction a system gives a kernel responder,
executable only through the program it was built from, since `SPComp` computations are not all
`ProbComp` programs.
-/

@[expose] public section

namespace CatCrypt.Crypto.VCVioBridge.ResponderSys

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.SDistrLift CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCConcrete
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {S : Type}

/-- A tagged answer: a query together with an answer to it. -/
abbrev Answer (spec : OracleSpec.{0, 0} ι) : Type := (t : spec.Domain) × spec.Range t

/-! ## `probCompLift` and functorial map -/

/-- `probCompLift` sends a functorial map to a bind into `SPComp.pure`. -/
theorem probCompLift_map {α β : Type} (f : α → β) (mx : ProbComp α) :
    probCompLift (f <$> mx) = SPComp.bind (probCompLift mx) fun a => SPComp.pure (f a) := by
  rw [map_eq_bind_pure_comp, probCompLift_bind]
  simp only [Function.comp_apply, probCompLift_pure]

/-- `SPComp.map` of a lift is the lift of the `ProbComp` map. -/
theorem map_probCompLift {α β : Type} (f : α → β) (mx : ProbComp α) :
    SPComp.map f (probCompLift mx) = probCompLift (f <$> mx) := by
  rw [probCompLift_map]; rfl

/-! ## Responders as systems, strategies as environments -/

/-- An executable responder from the state `r₀` as a reactive system: events are queries, and
the output of a step is the answer tagged with its query. -/
noncomputable def toSys (R : ProbResponder spec) [R.IsExecutable] (r₀ : R.State) :
    Sys R.State spec.Domain (Answer spec) where
  init := r₀
  step r t := probCompLift
    ((fun q => (q.2, (⟨t, q.1⟩ : Answer spec))) <$> ProbResponder.IsExecutable.answerComp r t)

/-- The strategy's update on a tagged answer: the answer to its exposed query advances the
state, an answer to another query leaves it unchanged. -/
noncomputable def absorb (A : OracleStrategy S spec) (s : S) (o : Answer spec) : S := by
  classical
  exact if h : o.1 = A.expose s then A.update s (h ▸ o.2) else s

/-- An answer to the exposed query is digested by `update`. -/
@[simp] theorem absorb_expose (A : OracleStrategy S spec) (s : S)
    (x : spec.Range (A.expose s)) : absorb A s ⟨A.expose s, x⟩ = A.update s x := by
  simp [absorb]

/-- An oracle strategy from the state `s₀` as an environment running `n` activations: it
issues its exposed query and absorbs the answer. -/
noncomputable def toStrat (A : OracleStrategy S spec) (s₀ : S) (n : ℕ) :
    Strat S spec.Domain (Answer spec) where
  rounds := n
  init := s₀
  next s := SPComp.pure (s, A.expose s)
  obs s o := SPComp.pure (absorb A s o)
  next_noFail _ := SPComp.pure_noFail _
  obs_noFail _ _ := SPComp.pure_noFail _

/-- Unfolding lemma of the step of `toSys`. -/
theorem toSys_step (R : ProbResponder spec) [R.IsExecutable] (r₀ r : R.State)
    (t : spec.Domain) :
    (toSys R r₀).step r t = probCompLift
      ((fun q => (q.2, (⟨t, q.1⟩ : Answer spec))) <$> ProbResponder.IsExecutable.answerComp r t) :=
  rfl

/-- Unfolding lemma of the event choice of `toStrat`. -/
theorem toStrat_next (A : OracleStrategy S spec) (s₀ s : S) (n : ℕ) :
    (toStrat A s₀ n).next s = SPComp.pure (s, A.expose s) := rfl

/-- Unfolding lemma of the observation of `toStrat`. -/
theorem toStrat_obs (A : OracleStrategy S spec) (s₀ s : S) (n : ℕ) (o : Answer spec) :
    (toStrat A s₀ n).obs s o = SPComp.pure (absorb A s o) := rfl

/-! ## Runs agree -/

/-- The joint run of the environment of a strategy against the system of a responder, without
bad flag, is the lift of VCVio's wired run `iterateAgainst`, with the states swapped. -/
theorem loop_toSys (R : ProbResponder spec) [R.IsExecutable] (A : OracleStrategy S spec)
    (r₀ : R.State) (s₀ : S) (m : ℕ) : ∀ (n : ℕ) (r : R.State) (s : S),
    loop (toSys R r₀) (fun _ => false) (toStrat A s₀ m) n (s, r, false) =
      probCompLift ((fun p => (p.2, p.1, false)) <$> OracleStrategy.iterateAgainst A R n (r, s))
  | 0, r, s => by
    rw [loop, OracleStrategy.iterateAgainst_zero, map_pure, probCompLift_pure]
  | n + 1, r, s => by
    rw [OracleStrategy.iterateAgainst_succ, OracleStrategy.stepAgainst_apply, map_bind,
      bind_map_left, probCompLift_bind]
    simp only [loop, toSys_step, toStrat_next, toStrat_obs, SPComp.pure_bind, probCompLift_map,
      SPComp.bind_assoc, absorb_expose, Bool.or_false, loop_toSys R A r₀ s₀ m n]

/-- The full run of `toStrat A s₀ n` against `toSys R r₀`. -/
theorem run_toSys (R : ProbResponder spec) [R.IsExecutable] (A : OracleStrategy S spec)
    (r₀ : R.State) (s₀ : S) (n : ℕ) :
    run (toSys R r₀) (fun _ => false) (toStrat A s₀ n) =
      probCompLift ((fun p => (p.2, p.1, false)) <$>
        OracleStrategy.iterateAgainst A R n (r₀, s₀)) :=
  loop_toSys R A r₀ s₀ n n r₀ s₀

/-- The view of the environment of a strategy against the system of a responder is the lift of
the strategy's final state in VCVio's wired run. -/
theorem view_toSys (R : ProbResponder spec) [R.IsExecutable] (A : OracleStrategy S spec)
    (r₀ : R.State) (s₀ : S) (n : ℕ) :
    view (toSys R r₀) (toStrat A s₀ n) =
      probCompLift (Prod.snd <$> OracleStrategy.iterateAgainst A R n (r₀, s₀)) := by
  rw [view, run_toSys, map_probCompLift, Functor.map_map]

/-! ## Transport of advantages and realization bounds -/

/-- The environment built from a strategy, the empty heap and a `ProbComp` distinguisher. -/
noncomputable def toEnv (A : OracleStrategy S spec) (s₀ : S) (n : ℕ) (D : S → ProbComp Bool) :
    Env (Strat S spec.Domain (Answer spec)) S where
  input := toStrat A s₀ n
  heap := CatCrypt.Core.Heap.empty
  dist s := probCompLift (D s)

/-- The VCVio game of a strategy against a responder for `n` rounds, judged by `D` on the
strategy's final state. -/
noncomputable def game (R : ProbResponder spec) [R.IsExecutable] (A : OracleStrategy S spec)
    (r₀ : R.State) (s₀ : S) (n : ℕ) (D : S → ProbComp Bool) : ProbComp Bool :=
  OracleStrategy.iterateAgainst A R n (r₀, s₀) >>= fun p => D p.2

/-- The advantage of the environment `toEnv A s₀ n D` between two translated responders is the
gap of the output masses of VCVio's games. -/
theorem adv_toSys (R₁ R₂ : ProbResponder spec) [R₁.IsExecutable] [R₂.IsExecutable]
    (A : OracleStrategy S spec) (r₁ : R₁.State) (r₂ : R₂.State) (s₀ : S) (n : ℕ)
    (D : S → ProbComp Bool) :
    adv (toSys R₁ r₁) (toSys R₂ r₂) (toEnv A s₀ n D) =
      absDiff (𝒟[game R₁ A r₁ s₀ n D] {true}) (𝒟[game R₂ A r₂ s₀ n D] {true}) := by
  simp only [adv_eq, toEnv, view_toSys, ← probCompLift_bind, prTrue_probCompLift, game,
    bind_map_left]

/-- A realization bound between two translated responders bounds the gap of VCVio's games of
every strategy and `ProbComp` distinguisher. -/
theorem gap_iterateAgainst_le_of_realizes (R₁ R₂ : ProbResponder spec) [R₁.IsExecutable]
    [R₂.IsExecutable] (r₁ : R₁.State) (r₂ : R₂.State)
    (bound : (ζ : Type) → Env (Strat ζ spec.Domain (Answer spec)) ζ → ℝ≥0∞)
    (h : Realizes (toSys R₁ r₁) (toSys R₂ r₂) bound)
    (A : OracleStrategy S spec) (s₀ : S) (n : ℕ) (D : S → ProbComp Bool) :
    absDiff (𝒟[game R₁ A r₁ s₀ n D] {true}) (𝒟[game R₂ A r₂ s₀ n D] {true}) ≤
      bound S (toEnv A s₀ n D) := by
  rw [← adv_toSys]
  exact h S (toEnv A s₀ n D)

/-! ## Systems as kernel responders -/

/-- The answer to the query `t` in a sub-distribution of tagged outputs: an output tagged with
another query is failure. -/
noncomputable def decode {τ : Type} (t : spec.Domain) (d : SDistr ((τ × Answer spec) × Heap)) :
    SDistr (spec.Range t × τ) := by
  classical
  exact SDistr.bind d fun c =>
    if h : c.1.2.1 = t then SDistr.pure (h ▸ c.1.2.2, c.1.1) else SDistr.fail

/-- A reactive system with tagged outputs, run from the heap `h`, as a kernel responder on its
discrete state space: the answer kernel at `t` is the measure of the decoded step. -/
noncomputable def ofSys {τ : Type} (Sy : Sys τ spec.Domain (Answer spec)) (h : Heap) :
    ProbResponder spec where
  State := τ
  instMeasurableSpaceState := ⊤
  instMeasurableSpaceRange _ := ⊤
  answerKernel t := by
    letI : MeasurableSpace τ := ⊤
    letI : MeasurableSpace (spec.Range t) := ⊤
    exact ⟨fun s => sdistrMeasure (decode t (Sy.step s t h)), measurable_from_top⟩
  answerKernel_isSubprobability t := by
    let _ : MeasurableSpace τ := ⊤
    let _ : MeasurableSpace (spec.Range t) := ⊤
    exact ⟨fun s => sdistrMeasure_apply_univ_le_one _⟩

/-- `ProbComp.toSDistr` sends a functorial map to a bind into `SDistr.pure`. -/
theorem toSDistr_map {α β : Type} (f : α → β) (mx : ProbComp α) :
    ProbComp.toSDistr (f <$> mx) =
      SDistr.bind (ProbComp.toSDistr mx) fun a => SDistr.pure (f a) := by
  rw [map_eq_bind_pure_comp, ProbComp.toSDistr_bind]
  rfl

/-- Decoding a step of `toSys R r₀` from any heap gives the answer program of `R`, read in
`SDistr`. -/
theorem decode_toSys_step (R : ProbResponder spec) [R.IsExecutable] (r₀ s : R.State)
    (t : spec.Domain) (h : Heap) :
    decode t ((toSys R r₀).step s t h) =
      ProbComp.toSDistr (ProbResponder.IsExecutable.answerComp s t) := by
  simp only [decode, toSys_step, probCompLift_eq, sdistrToSPComp_run, toSDistr_map,
    SDistr.bind_assoc, SDistr.pure_bind, dite_true]
  exact SDistr.bind_pure _

/-- Translating a stateful handler to a system and back to a responder gives the answer kernel
of the handler's responder, from every heap. -/
theorem ofSys_toSys_answerKernel {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (r₀ : σ) (h : Heap) (t : spec.Domain) (s : σ) :
    (ofSys (toSys (ProbResponder.ofQueryImpl impl) r₀) h).answerKernel t s =
      (ProbResponder.ofQueryImpl impl).answerKernel t s := by
  let _ : MeasurableSpace σ := ⊤
  let _ : MeasurableSpace (spec.Range t) := ⊤
  rw [ProbResponder.IsExecutable.answerKernel_eq_evalDist, evalDist_toSDistr, evalDist_sdistr,
    ← decode_toSys_step (ProbResponder.ofQueryImpl impl) r₀ s t h]
  rfl

end CatCrypt.Crypto.VCVioBridge.ResponderSys
