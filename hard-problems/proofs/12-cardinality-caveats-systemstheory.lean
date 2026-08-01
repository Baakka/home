import Mathlib

/-!
This snippet is about:

  IsOptimal
  exponential_policy_space_with_flat_objective

found at line 689 of 693, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Inlined dependency: LeanTest/HardProblems/Core.lean -/


/-!
# Core partially observed system

The companion modules share one small stochastic interface: a state transition
kernel controlled by an action and an observation kernel on the resulting state
space. More specialized task, policy, horizon, cost, and resource parameters
are introduced in the modules that use them.
-/

namespace HardProblems

/-- A countably supported partially observed stochastic system. The transition
kernel is action-indexed; the observation kernel emits a law from each latent
state. Admissible policy classes and resource bounds are separate parameters. -/
structure POSystem (S A O : Type*) where
  T : S → A → PMF S
  Z : S → PMF O

end HardProblems


/-! Inlined dependency: LeanTest/HardProblems/Observability.lean -/


/-!
# Observability and belief updates

Observational equivalence, decision-critical ambiguity, robust actions, and
the belief-state update.

Results proved here:

* `obsEquiv_equivalence`: observational equivalence (equality of the
  observation-process law under every probing policy and horizon) is an
  equivalence relation.
* `robustSet_eq_iInter`: a robust action is exactly a member of the
  intersection of acceptable sets over the equivalence class.
* `robustlyInfeasible_iff_iInter_eq_empty`: robust choice fails exactly when
  that total intersection is empty.
* `DecisionCritical.no_robust_action`: a disjoint equivalent pair is one
  sufficient certificate of robust infeasibility.
* `bayesUpdate`: the canonical belief update. Its well-definedness hypothesis
  `bayesEvidence ≠ 0` is not a technicality: it fails exactly when the
  observation has zero predictive probability under the maintained model.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

variable {S A O : Type*}

/-- The law of the focal observation sequence: run the maintained model `M`
for `n` steps from state `s` under a probing policy `π` (a function of the
observation history), returning the distribution over observation histories.
The accumulator `h` carries observations already made.

Timing convention: each round observes the current state, extends the history,
chooses an action, and then transitions. An `n`-round run therefore emits `n`
observations from `s_0, ..., s_(n-1)`; the terminal state `s_n` is not observed.
The Bayes definitions below are separate and use a predict-then-observe step. -/
def obsProcess (M : POSystem S A O) (π : List O → PMF A) :
    ℕ → S → List O → PMF (List O)
  | 0, _, h => PMF.pure h
  | n + 1, s, h =>
    (M.Z s).bind fun o =>
      (π (h ++ [o])).bind fun a =>
        (M.T s a).bind fun s' =>
          obsProcess M π n s' (h ++ [o])

/-- Observational equivalence: no policy of the declared function type
distinguishes the two states at any finite horizon. -/
def ObsEquiv (M : POSystem S A O) (s s' : S) : Prop :=
  ∀ (π : List O → PMF A) (n : ℕ), obsProcess M π n s [] = obsProcess M π n s' []

/-- Observational equivalence is an equivalence relation, as the notation
`≡` silently promises. -/
theorem obsEquiv_equivalence (M : POSystem S A O) : Equivalence (ObsEquiv M) where
  refl _ := fun _ _ => rfl
  symm h := fun π n => (h π n).symm
  trans h₁ h₂ := fun π n => (h₁ π n).trans (h₂ π n)

/-- Decision-critical ambiguity: two observationally equivalent states whose
acceptable-action sets `A*_M` are disjoint. -/
def DecisionCritical (M : POSystem S A O) (Astar : S → Set A) (s s' : S) : Prop :=
  ObsEquiv M s s' ∧ Disjoint (Astar s) (Astar s')

/-- An action is robust at `s` when it is acceptable in every state
observationally equivalent to `s`. -/
def RobustAcceptable (M : POSystem S A O) (Astar : S → Set A) (s : S) (a : A) : Prop :=
  ∀ s', ObsEquiv M s s' → a ∈ Astar s'

/-- Robust actions are exactly the intersection of the acceptable sets over
the equivalence class of `s`. -/
theorem robustSet_eq_iInter (M : POSystem S A O) (Astar : S → Set A) (s : S) :
    {a | RobustAcceptable M Astar s a} = ⋂ s' ∈ {s' | ObsEquiv M s s'}, Astar s' := by
  ext a
  simp [RobustAcceptable]

/-- Robust choice is infeasible when no action is acceptable throughout the
observational equivalence class. -/
def RobustlyInfeasible (M : POSystem S A O) (Astar : S → Set A) (s : S) : Prop :=
  ¬ ∃ a, RobustAcceptable M Astar s a

/-- The exact criterion for robust infeasibility is emptiness of the total
intersection of acceptable-action sets over the observational class. Pairwise
disjointness is sufficient but not necessary for this intersection to be empty. -/
theorem robustlyInfeasible_iff_iInter_eq_empty
    (M : POSystem S A O) (Astar : S → Set A) (s : S) :
    RobustlyInfeasible M Astar s ↔
      ⋂ s' ∈ {s' | ObsEquiv M s s'}, Astar s' = ∅ := by
  rw [← robustSet_eq_iInter]
  change (¬ ({a | RobustAcceptable M Astar s a} : Set A).Nonempty) ↔ _
  exact Set.not_nonempty_iff_eq_empty

/-- A disjoint observationally equivalent pair certifies that no robust action
exists at the first state. -/
theorem DecisionCritical.no_robust_action
    {M : POSystem S A O} {Astar : S → Set A} {s s' : S}
    (h : DecisionCritical M Astar s s') :
    ¬∃ a, RobustAcceptable M Astar s a := by
  rintro ⟨a, ha⟩
  have h₁ : a ∈ Astar s := ha s ((obsEquiv_equivalence M).refl s)
  have h₂ : a ∈ Astar s' := ha s' h.1
  exact Set.disjoint_left.mp h.2 h₁ h₂

/-! ## The belief update

Given a prior belief `b`, an action-marginalized step kernel
`step = T_{θ,π₋₀}(· ∣ ·, a)`, and an observation kernel `Z`, the posterior
weight of `s'` is `Z s' o * (b.bind step) s'`, normalized by the total
predictive probability of the observation. -/

variable (b : PMF S) (step : S → PMF S) (Z : S → PMF O) (o : O)

/-- Predictive probability of observing `o` after one step from belief `b`:
the normalizer of Bayes' rule. -/
def bayesEvidence : ℝ≥0∞ :=
  ∑' s', Z s' o * (b.bind step) s'

/-- The evidence never exceeds one, hence is finite. -/
theorem bayesEvidence_le_one : bayesEvidence b step Z o ≤ 1 := by
  have h : ∀ s', Z s' o * (b.bind step) s' ≤ (b.bind step) s' := fun s' =>
    mul_le_of_le_one_left' (PMF.coe_le_one _ _)
  calc bayesEvidence b step Z o ≤ ∑' s', (b.bind step) s' := ENNReal.tsum_le_tsum h
    _ = 1 := (b.bind step).tsum_coe

/-- The canonical belief update. The hypothesis states that the observation has
positive probability under the current one-step predictive law. The definition
does not contain a model class or prescribe a response to zero evidence. -/
def bayesUpdate (h : bayesEvidence b step Z o ≠ 0) : PMF S :=
  PMF.normalize (fun s' => Z s' o * (b.bind step) s') h
    (lt_of_le_of_lt (bayesEvidence_le_one b step Z o) ENNReal.one_lt_top).ne

/-- The posterior is the likelihood-times-prediction, renormalized. -/
theorem bayesUpdate_apply (h : bayesEvidence b step Z o ≠ 0) (s' : S) :
    bayesUpdate b step Z o h s' =
      Z s' o * (b.bind step) s' * (bayesEvidence b step Z o)⁻¹ :=
  rfl

/-- The belief update extended by a declared default: when the observation has
zero predictive probability, keep the one-step prediction. The barycentre
theorem below does not depend on the choice on that zero-weight branch. -/
noncomputable def bayesUpdateOr : PMF S :=
  if h : bayesEvidence b step Z o ≠ 0 then bayesUpdate b step Z o h
  else b.bind step

/-- Barycentre consistency of Bayesian updating: the posterior, averaged over
the predictive observation law, is exactly the one-step prediction. This
identity does not say that individual posteriors are unchanged. -/
theorem tsum_bayesEvidence_mul_bayesUpdateOr (s' : S) :
    ∑' o, bayesEvidence b step Z o * bayesUpdateOr b step Z o s'
      = (b.bind step) s' := by
  have key : ∀ o : O, bayesEvidence b step Z o * bayesUpdateOr b step Z o s'
      = Z s' o * (b.bind step) s' := by
    intro o
    by_cases h : bayesEvidence b step Z o = 0
    · have hz : Z s' o * (b.bind step) s' = 0 := by
        have hle : Z s' o * (b.bind step) s' ≤ bayesEvidence b step Z o :=
          ENNReal.le_tsum s'
        simpa [h, nonpos_iff_eq_zero] using hle
      rw [h, zero_mul, hz]
    · have hfin : bayesEvidence b step Z o ≠ ⊤ :=
        (lt_of_le_of_lt (bayesEvidence_le_one b step Z o) ENNReal.one_lt_top).ne
      unfold bayesUpdateOr
      rw [dif_pos h, bayesUpdate_apply, mul_left_comm,
        ENNReal.mul_inv_cancel h hfin, mul_one]
  rw [tsum_congr key, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ## The belief-MDP bridge

The belief process is itself a Markov process on `PMF S`: sample the next
observation from its predictive law, update. `evidencePMF` packages the
Bayes normalizers as that predictive law (total mass one is Fubini), and
`beliefKernel` is the resulting one-step kernel on belief space. -/

/-- The predictive law of the next observation under belief `b`: the Bayes
normalizers, packaged as a distribution over observations. -/
def evidencePMF (b : PMF S) (step : S → PMF S) (Z : S → PMF O) : PMF O :=
  ⟨fun o => bayesEvidence b step Z o, by
    have h : ∑' o, bayesEvidence b step Z o = 1 := by
      unfold bayesEvidence
      rw [ENNReal.tsum_comm]
      calc ∑' s', ∑' o, Z s' o * (b.bind step) s'
          = ∑' s', (∑' o, Z s' o) * (b.bind step) s' :=
            tsum_congr fun s' => ENNReal.tsum_mul_right
        _ = ∑' s', (b.bind step) s' := by simp
        _ = 1 := (b.bind step).tsum_coe
    rw [← h]
    exact ENNReal.summable.hasSum⟩

@[simp] theorem evidencePMF_apply (o : O) :
    evidencePMF b step Z o = bayesEvidence b step Z o :=
  rfl

/-- One Markov step of the belief process: draw the observation from its
predictive law, then update. Beliefs thereby evolve as an ordinary Markov
process on the space `PMF S` under the supplied update rule. -/
def beliefKernel (step : S → PMF S) (Z : S → PMF O) (b : PMF S) : PMF (PMF S) :=
  (evidencePMF b step Z).bind fun o => PMF.pure (bayesUpdateOr b step Z o)

/-- Barycenter consistency of the belief kernel: averaging the next belief
over the observation law is the one-step prediction. Observations move
beliefs around; their mean moves by the dynamics alone. -/
theorem beliefKernel_bind_id (b : PMF S) (step : S → PMF S) (Z : S → PMF O) :
    (beliefKernel step Z b).bind id = b.bind step := by
  ext s'
  rw [beliefKernel, PMF.bind_bind]
  simp only [PMF.pure_bind, id_eq]
  rw [PMF.bind_apply]
  exact tsum_bayesEvidence_mul_bayesUpdateOr b step Z s'

/-! ## Zero evidence and full-support contamination

A zero normalizer means that every state with positive predictive mass assigns
zero likelihood to the observation. Adding a positive-weight full-support
contamination component makes every observation have positive predictive
probability. These are properties of the declared probability laws; they do
not formalize a class of models or a revision procedure. -/

/-- The localization: evidence dies exactly when every state the prediction
reaches makes the observation impossible. -/
theorem bayesEvidence_eq_zero_iff :
    bayesEvidence b step Z o = 0 ↔
      ∀ s', Z s' o = 0 ∨ (b.bind step) s' = 0 := by
  rw [bayesEvidence, ENNReal.tsum_eq_zero]
  exact forall_congr' fun s' => mul_eq_zero

/-- ε-contamination of an observation model: with weight `1 - ε` observe
through `Z`, with weight `ε` through the contamination `ζ`. -/
def contaminate (ε : ℝ≥0∞) (hε : ε ≤ 1) (Zobs ζ : S → PMF O) :
    S → PMF O := fun s =>
  ⟨fun o' => (1 - ε) * Zobs s o' + ε * ζ s o', by
    have h : ∑' o', ((1 - ε) * Zobs s o' + ε * ζ s o') = 1 := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        (Zobs s).tsum_coe, (ζ s).tsum_coe, mul_one, mul_one,
        tsub_add_cancel_of_le hε]
    have hs : HasSum (fun o' => (1 - ε) * Zobs s o' + ε * ζ s o')
        (∑' o', ((1 - ε) * Zobs s o' + ε * ζ s o')) := ENNReal.summable.hasSum
    rw [h] at hs
    exact hs⟩

/-- If the contamination component has full support and positive mixture
weight, every observation has positive evidence under the contaminated
kernel, for every prior and step kernel. -/
theorem bayesEvidence_mixture_pos (Zobs ζ : S → PMF O) {ε : ℝ≥0∞}
    (hε : ε ≤ 1) (hε0 : ε ≠ 0) (hζ : ∀ s o', ζ s o' ≠ 0) :
    bayesEvidence b step (contaminate ε hε Zobs ζ) o ≠ 0 := by
  intro h
  rw [bayesEvidence_eq_zero_iff] at h
  have hpred : ∀ s', (b.bind step) s' = 0 := by
    intro s'
    rcases h s' with h1 | h2
    · exfalso
      have hval : (contaminate ε hε Zobs ζ) s' o
          = (1 - ε) * Zobs s' o + ε * ζ s' o := rfl
      rw [hval, add_eq_zero] at h1
      rcases mul_eq_zero.mp h1.2 with hA | hB
      · exact hε0 hA
      · exact hζ s' o hB
    · exact h2
  have hone : (1 : ℝ≥0∞) = 0 := by
    rw [← (b.bind step).tsum_coe, tsum_congr hpred, tsum_zero]
  exact one_ne_zero hone

end

end HardProblems


/-! Target module: LeanTest/HardProblems/SystemsTheory.lean -/


/-!
# Counting, probing, statistics, and value of information

This file collects independent formal results used by the manuscript:

* `requisite_variety`: a response rule that uses few distinct responses
  cannot confine many distinguishable disturbances to a small outcome set.
  The counting form: |D| is at most (responses used) times (outcomes hit).
* `PassivelyDistinguishable` / `ProbeDistinguishable`: some model pairs agree
  under a selected constant action but differ under another policy.
* `statistic_based_rule_fails`: a decision rule that
  acts only through a summary statistic inherits the statistic's blindness.
* `invariance_comp` / `increment_bound_not_compositional`: set invariance is
  closed under composition, while the same unit increment bound is not.
* `value_of_information_nonneg`: optimizing after observing an outcome never
  lowers the nonnegatively weighted utility optimum.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

/-! ## Finite response and outcome counting -/

section Counting

variable {D A O : Type*}

/-- The separation a counting bound actually needs: two disturbances that the
regulator answers the same way must be told apart by that shared response.
Nothing is required of responses the rule never issues, or of pairs it answers
differently, because the bound already charges for the difference in response.

Demanding that *every* response separate *every* pair, which is how the law is
usually stated informally, is sufficient but strictly stronger:
`fiberSeparating_of_injective` gives the implication and
`fiberSeparating_strictly_weaker` witnesses that it does not reverse. -/
def FiberSeparating (ω : D → A → O) (ρ : D → A) : Prop :=
  ∀ d d', ρ d = ρ d' → ω d (ρ d) = ω d' (ρ d') → d = d'

/-- The informal premise implies the one the counting argument uses. -/
theorem fiberSeparating_of_injective (ω : D → A → O)
    (hinj : ∀ a, Function.Injective fun d => ω d a) (ρ : D → A) :
    FiberSeparating ω ρ := by
  intro d d' h1 h2
  apply hinj (ρ d)
  show ω d (ρ d) = ω d' (ρ d)
  rw [h2, ← h1]

/-- Finite counting form. `ω d a` is the outcome
of disturbance `d` under regulator response `a`. If the response rule `ρ`
separates the disturbances it answers alike (`FiberSeparating`), then the
number of disturbances is at most the number of responses actually used times
the number of outcomes actually hit. -/
theorem requisite_variety [Fintype D] [DecidableEq A] [DecidableEq O]
    (ω : D → A → O) (ρ : D → A) (hsep : FiberSeparating ω ρ) :
    Fintype.card D ≤
      (Finset.univ.image ρ).card * (Finset.univ.image fun d => ω d (ρ d)).card := by
  have key :
      (Finset.univ : Finset D).card ≤
        ((Finset.univ.image ρ) ×ˢ (Finset.univ.image fun d => ω d (ρ d))).card := by
    apply Finset.card_le_card_of_injOn (fun d => (ρ d, ω d (ρ d)))
    · intro d _
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem ρ (Finset.mem_univ d),
         Finset.mem_image_of_mem _ (Finset.mem_univ d)⟩
    · intro d _ d' _ hdd
      exact hsep d d' (congrArg Prod.fst hdd) (congrArg Prod.snd hdd)
  rw [Finset.card_product] at key
  simpa using key

/-- The separation premise is load-bearing, not decoration. Drop it and the
inequality is false: two disturbances, one response, one outcome gives
`2 ≤ 1 * 1`. -/
theorem requisite_variety_fails_without_separation :
    ¬ ∀ (ω : Bool → Unit → Unit) (ρ : Bool → Unit),
        Fintype.card Bool ≤
          (Finset.univ.image ρ).card *
            (Finset.univ.image fun d => ω d (ρ d)).card := by
  intro h
  have := h (fun _ _ => ()) (fun _ => ())
  simp at this

/-- Fiberwise separation is strictly weaker than separation under every fixed
response. The rule `ρ = id` answers each disturbance its own way, so every
fiber is a singleton and separation is free, while the response `false`
collapses both disturbances to the same outcome. A bound that assumed the
informal premise would exclude this regulator for no reason. -/
theorem fiberSeparating_strictly_weaker :
    ∃ (ω : Bool → Bool → Bool) (ρ : Bool → Bool),
      FiberSeparating ω ρ ∧ ¬ ∀ a, Function.Injective fun d => ω d a := by
  refine ⟨fun d a => if a then d else false, id, ?_, ?_⟩
  · intro d d' h1 _
    exact h1
  · intro hinj
    have := hinj false (a₁ := true) (a₂ := false) rfl
    simp at this

/-- Perfect regulation: holding the outcome constant requires at least as
much response variety as there is disturbance variety. -/
theorem requisite_variety_perfect [Fintype D] [DecidableEq A] [DecidableEq O]
    (ω : D → A → O) (ρ : D → A) (hsep : FiberSeparating ω ρ)
    (o₀ : O) (hperf : ∀ d, ω d (ρ d) = o₀) :
    Fintype.card D ≤ (Finset.univ.image ρ).card := by
  have h := requisite_variety ω ρ hsep
  have himg : (Finset.univ.image fun d => ω d (ρ d)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d', _, rfl⟩ := Finset.mem_image.mp hy
    rw [hperf d, hperf d']
  calc Fintype.card D
      ≤ (Finset.univ.image ρ).card * (Finset.univ.image fun d => ω d (ρ d)).card := h
    _ ≤ (Finset.univ.image ρ).card * 1 :=
        Nat.mul_le_mul_left _ himg
    _ = (Finset.univ.image ρ).card := Nat.mul_one _

end Counting

/-! ## Constant-action and policy-dependent distinguishability -/

section Probes

variable {S A O : Type*}

/-- Two models are distinguishable from `s` under the constant action `a₀`
when their observation-history laws differ at some horizon. The type does not
assert that `a₀` is inert; that interpretation is supplied by an application. -/
def PassivelyDistinguishable (M₁ M₂ : POSystem S A O) (a₀ : A) (s : S) : Prop :=
  ∃ n, obsProcess M₁ (fun _ => PMF.pure a₀) n s [] ≠
        obsProcess M₂ (fun _ => PMF.pure a₀) n s []

/-- Two models are probe distinguishable from `s` when some policy of the
declared function type separates their observation-history laws. -/
def ProbeDistinguishable (M₁ M₂ : POSystem S A O) (s : S) : Prop :=
  ∃ (π : List O → PMF A) (n : ℕ),
    obsProcess M₁ π n s [] ≠ obsProcess M₂ π n s []

/-- A constant-action policy is a special case of an observation-dependent
policy. -/
theorem passively_imp_probe {M₁ M₂ : POSystem S A O} {a₀ : A} {s : S}
    (h : PassivelyDistinguishable M₁ M₂ a₀ s) : ProbeDistinguishable M₁ M₂ s :=
  let ⟨n, hn⟩ := h
  ⟨fun _ => PMF.pure a₀, n, hn⟩

/-- If two models agree on the observation kernel and on the transition kernel
at `a₀`, their laws under the constant-`a₀` policy agree at every horizon. -/
theorem obsProcess_congr_null (M₁ M₂ : POSystem S A O) (a₀ : A)
    (hZ : M₁.Z = M₂.Z) (hT : ∀ s, M₁.T s a₀ = M₂.T s a₀) :
    ∀ (n : ℕ) (s : S) (h : List O),
      obsProcess M₁ (fun _ => PMF.pure a₀) n s h =
        obsProcess M₂ (fun _ => PMF.pure a₀) n s h := by
  intro n
  induction n with
  | zero => intro s h; rfl
  | succ n ih =>
    intro s h
    simp only [obsProcess, PMF.pure_bind, hZ, hT, ih]

/-- Witness model: the state is observed exactly, the passive action `false`
leaves the state alone, and the probe action `true` flips it. -/
noncomputable def flipModel : POSystem Bool Bool Bool where
  T := fun s a => PMF.pure (if a then !s else s)
  Z := fun s => PMF.pure s

/-- Witness model: the state is observed exactly and never changes, whatever
the action. -/
noncomputable def inertModel : POSystem Bool Bool Bool where
  T := fun s _ => PMF.pure s
  Z := fun s => PMF.pure s

/-- There are two Boolean models whose laws agree under the constant action
`false` at every horizon but differ under the constant action `true`. In these
witness models, `false` is inert and `true` changes one model only. -/
theorem exists_probe_only_distinguishable :
    ∃ (M₁ M₂ : POSystem Bool Bool Bool) (s : Bool),
      ¬ PassivelyDistinguishable M₁ M₂ false s ∧ ProbeDistinguishable M₁ M₂ s := by
  refine ⟨flipModel, inertModel, false, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    exact hn (obsProcess_congr_null flipModel inertModel false rfl
      (fun s => by simp [flipModel, inertModel]) n false [])
  · refine ⟨fun _ => PMF.pure true, 2, ?_⟩
    have h₁ : obsProcess flipModel (fun _ => PMF.pure true) 2 false [] =
        PMF.pure [false, true] := by
      simp [obsProcess, flipModel, PMF.pure_bind]
    have h₂ : obsProcess inertModel (fun _ => PMF.pure true) 2 false [] =
        PMF.pure [false, false] := by
      simp [obsProcess, inertModel, PMF.pure_bind]
    rw [h₁, h₂]
    intro hcontra
    have := congrArg (fun p => p [false, true]) hcontra
    simp [PMF.pure_apply] at this

end Probes

/-! ## Statistic-factorized rules -/

section Statistics

variable {S A : Type*}

/-- A decision rule that acts only through a summary statistic inherits the
statistic's blindness: if the statistic identifies two states whose
acceptable-action sets are disjoint, then every rule based on it acts
unacceptably in at least one of the two. This is a sufficient pairwise
obstruction, not an exact characterization of safe statistic-based choice. -/
theorem statistic_based_rule_fails {m : S → ℝ} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : ℝ → A) :
    α (m s) ∉ Astar s ∨ α (m s') ∉ Astar s' := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  rw [hm] at h1
  exact Set.disjoint_left.mp hdisj h1 h2

/-- The statistic-factorization obstruction with an arbitrary statistic
codomain; nothing in the argument uses the real numbers. -/
theorem statistic_based_rule_fails' {Y : Type*} {m : S → Y} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : Y → A) :
    α (m s) ∉ Astar s ∨ α (m s') ∉ Astar s' := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  rw [hm] at h1
  exact Set.disjoint_left.mp hdisj h1 h2

/-- The randomized version: a stochastic rule that acts only through the
statistic cannot be supported inside both acceptable sets either. Whatever
it randomizes over, some realization it actually plays is unacceptable in
one of the two conflated states. -/
theorem statistic_based_randomized_rule_fails {m : S → ℝ} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : ℝ → PMF A) :
    ¬((α (m s)).support ⊆ Astar s ∧ (α (m s')).support ⊆ Astar s') := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := (α (m s)).support_nonempty
  have ha' : a ∈ (α (m s')).support := by rw [← hm]; exact ha
  exact Set.disjoint_left.mp hdisj (h1 ha) (h2 ha')

/-! `statistic_based_randomized_rule_fails` reads "acts unacceptably" as
playing an unacceptable action somewhere in the support, which is the right
reading for a `PMF` and gets normalization for free, since a `PMF` sums to one
by construction. It is the wrong reading for a distribution with no atoms at
all: a continuous law can be supported entirely outside the acceptable set
while every single action has probability zero, and a support-based statement
says nothing useful there.

So the same obstruction is stated once more for an arbitrary probability
measure, where acting unacceptably means failing to be *almost surely*
acceptable. The acceptable sets need not even be measurable, because the
conclusion is phrased through almost-everywhere membership rather than through
the measure of a complement.

This generalization is Aristotle's, from an independent formalization of the
same informal claim; the support-based version above is this project's. Its own
discrete formulation rolled a distribution structure by hand and then needed
normalization as an explicit side condition, with a counterexample showing why.
Using mathlib's `PMF` and `ProbabilityMeasure` sidesteps that entirely, so only
the generalization is kept here. -/

/-- `f` factors through `q` when all information used by `f` passes through
`q`. -/
def FactorsThrough {X Q Y : Type*} (f : X → Y) (q : X → Q) : Prop :=
  ∃ g : Q → Y, f = g ∘ q

/-- A function factoring through a map is constant on each fibre of that map. -/
theorem FactorsThrough.eq_of_eq {X Q Y : Type*} {f : X → Y} {q : X → Q}
    (hf : FactorsThrough f q) {x y : X} (hxy : q x = q y) : f x = f y := by
  obtain ⟨g, hg⟩ := hf
  simp [hg, hxy]

/-- A measure-theoretic randomized decision is acceptable at `s` when it is
supported on acceptable actions up to a null set. -/
def AlmostSurelyAcceptableAt {State Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action)
    (decision : State → MeasureTheory.ProbabilityMeasure Action) (s : State) : Prop :=
  ∀ᵐ a ∂(decision s : MeasureTheory.Measure Action), a ∈ acceptable s

/-- For an arbitrary probability measure, “acts unacceptably” means failure to
be almost surely supported on the acceptable set.  When the set is measurable,
this is equivalent to assigning positive mass to its complement. -/
def MeasureRandomizedUnacceptableAt {State Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action)
    (decision : State → MeasureTheory.ProbabilityMeasure Action) (s : State) : Prop :=
  ¬ AlmostSurelyAcceptableAt acceptable decision s

private lemma probabilityMeasure_not_ae_false {Action : Type*} [MeasurableSpace Action]
    (p : MeasureTheory.ProbabilityMeasure Action) :
    ¬ (∀ᵐ _a ∂(p : MeasureTheory.Measure Action), False) := by
  intro h
  rw [MeasureTheory.ae_iff] at h
  have hu : {_a : Action | ¬ False} = Set.univ := by ext; simp
  rw [hu] at h
  exact MeasureTheory.IsProbabilityMeasure.ne_zero (p : MeasureTheory.Measure Action)
    (MeasureTheory.Measure.measure_univ_eq_zero.mp h)

/-- The randomized obstruction for completely general probability measures.
No countability or measurability of the acceptable sets is required. -/
theorem measure_randomized_factoring_disjoint_obstruction
    {State Signal Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action) (signal : State → Signal)
    (decision : State → MeasureTheory.ProbabilityMeasure Action)
    (hfactor : FactorsThrough decision signal) {x y : State}
    (hidentified : signal x = signal y)
    (hdisjoint : Disjoint (acceptable x) (acceptable y)) :
    MeasureRandomizedUnacceptableAt acceptable decision x ∨
      MeasureRandomizedUnacceptableAt acceptable decision y := by
  have heq : decision x = decision y := hfactor.eq_of_eq hidentified
  by_cases hx : AlmostSurelyAcceptableAt acceptable decision x
  · right
    intro hy
    unfold AlmostSurelyAcceptableAt at hx hy
    rw [← heq] at hy
    have hb := hx.and hy
    have hf : ∀ᵐ _a ∂(decision x : MeasureTheory.Measure Action), False :=
      hb.mono (fun _a ha => hdisjoint.le_bot ha)
    exact probabilityMeasure_not_ae_false (decision x) hf
  · exact Or.inl hx

/-- Statistic-factorized form of the general probability-measure obstruction. -/
theorem measure_randomized_statistic_rule_disjoint_obstruction
    {State Statistic Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action) (statistic : State → Statistic)
    (rule : Statistic → MeasureTheory.ProbabilityMeasure Action) {x y : State}
    (hidentified : statistic x = statistic y)
    (hdisjoint : Disjoint (acceptable x) (acceptable y)) :
    MeasureRandomizedUnacceptableAt acceptable (rule ∘ statistic) x ∨
      MeasureRandomizedUnacceptableAt acceptable (rule ∘ statistic) y := by
  apply measure_randomized_factoring_disjoint_obstruction acceptable statistic
    (rule ∘ statistic) ⟨rule, rfl⟩ hidentified hdisjoint

end Statistics

/-! ## Set invariance and increment bounds under composition -/

section Composition

/-- Set invariance is closed under composition: if each component maps the
set into itself, so does the composite. -/
theorem invariance_comp {S : Type*} {C : Set S} {f g : S → S}
    (hf : Set.MapsTo f C C) (hg : Set.MapsTo g C C) :
    Set.MapsTo (g ∘ f) C C :=
  hg.comp hf

/-- The same unit increment bound is not closed under composition: two
functions that each move every point by at most one can jointly move a point
by two. -/
theorem increment_bound_not_compositional :
    ∃ f g : ℝ → ℝ,
      (∀ x, |f x - x| ≤ 1) ∧ (∀ x, |g x - x| ≤ 1) ∧
      ∃ x : ℝ, ¬ (|(g ∘ f) x - x| ≤ 1) := by
  refine ⟨fun x => x + 1, fun x => x + 1, fun x => by norm_num,
    fun x => by norm_num, 0, ?_⟩
  norm_num [Function.comp]

/-- Cardinality of the full deterministic state-feedback policy space. This is
a counting identity, not a computational lower bound. -/
theorem card_policySpace (S A : Type*) [Fintype S] [Fintype A] [DecidableEq S] :
    Fintype.card (S → A) = Fintype.card A ^ Fintype.card S :=
  Fintype.card_fun

/-- A point is globally optimal for a natural-valued objective. -/
def IsOptimal {P : Type*} (J : P → ℕ) (p : P) : Prop :=
  ∀ q, J q ≤ J p

/-- Exponential policy-space cardinality alone is not an optimization lower
bound: a constant objective makes every Boolean policy globally optimal. Ported
from the Aristotle target `CapacityCaveat`. -/
theorem exponential_policy_space_with_flat_objective (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n ∧
      ∀ p : Fin n → Bool, IsOptimal (fun _ => 0) p := by
  constructor
  · simp
  · simp [IsOptimal]

end Composition
end
end HardProblems
