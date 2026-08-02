import Mathlib

/-!
This snippet is about:

  Indist
  indist_equivalence
  ExperimentRefines
  experimentRefines_refl
  experimentRefines_trans
  indist
  RobustActions
  robustActions_mono
  indist_iff_of_mutual_refinement
  robustActions_eq_of_mutual_refinement
  quotient_strict_decision_loss

found at line 1049 of 1055, near the end of this file.

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
* `common_estimate_forces_pairwise_convergence`: if one estimate converges to
  each of two trajectories, those trajectories converge to one another. This
  is the metric core of a necessary detectability condition.
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

open Filter
open scoped ENNReal Topology

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

/-- A necessary metric condition for asymptotic reconstruction: if the same
estimate converges to each of two state trajectories, their mutual distance
converges to zero. To turn this into a detectability theorem, a system-specific
argument must show that observationally indistinguishable trajectories really
feed the same estimate. -/
theorem common_estimate_forces_pairwise_convergence
    {X : Type*} [PseudoMetricSpace X] (x₁ x₂ xhat : ℕ → X)
    (h₁ : Tendsto (fun t => dist (x₁ t) (xhat t)) atTop (𝓝 0))
    (h₂ : Tendsto (fun t => dist (x₂ t) (xhat t)) atTop (𝓝 0)) :
    Tendsto (fun t => dist (x₁ t) (x₂ t)) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => dist_nonneg) (fun t => dist_triangle _ (xhat t) _) ?_
  have h₂' : Tendsto (fun t => dist (xhat t) (x₂ t)) atTop (𝓝 0) :=
    h₂.congr' (Eventually.of_forall fun t => dist_comm (x₂ t) (xhat t))
  simpa only [zero_add] using h₁.add h₂'

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


/-! Inlined dependency: LeanTest/HardProblems/SystemsTheory.lean -/


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

/-- For a product of a finite state space and its deterministic policy space,
the separating-response hypothesis yields the explicit lower bound
`|S| * |A| ^ |S|` on the number of realized responses. -/
theorem requisite_variety_augmented {S A R O : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq R] [DecidableEq O]
    (ω : S × (S → A) → R → O) (ρ : S × (S → A) → R)
    (hsep : FiberSeparating ω ρ) (o₀ : O) (hperf : ∀ d, ω d (ρ d) = o₀) :
    Fintype.card S * Fintype.card A ^ Fintype.card S ≤
      (Finset.univ.image ρ).card := by
  have h := requisite_variety_perfect ω ρ hsep o₀ hperf
  rwa [Fintype.card_prod, card_policySpace] at h

/-- Semantic drift: the syntax is fixed while its interpretation changes over
time. -/
def SemanticDrift {W B : Type*} (sem : ℕ → W → B) : Prop :=
  ∃ t x, sem (t + 1) x ≠ sem t x

/-- A finite witness in which one predicate of an interpretation holds at time
zero and fails at time one while the interpreted syntax remains fixed. -/
theorem contract_check_time_indexed :
    ∃ (sem : ℕ → Bool → Bool) (contract : (Bool → Bool) → Prop),
      contract (sem 0) ∧ SemanticDrift sem ∧ ¬contract (sem 1) := by
  refine ⟨fun t => if t = 0 then id else not, fun f => f true = true, ?_, ⟨0, true, ?_⟩, ?_⟩
  · simp
  · simp
  · simp

end Composition

/-! ## Weighted value of observation -/

section ValueInformation

variable {A O : Type*} [Fintype A] [Fintype O] [Nonempty A]

/-- For nonnegative outcome weights, choosing after observing the outcome never
lowers the weighted utility optimum. If the weights sum to one, they may be
read as a predictive distribution. The left side optimizes one action before
the outcome; the right side optimizes an action separately at each outcome. -/
theorem value_of_information_nonneg (u : A → O → ℝ) (w : O → ℝ)
    (hw : ∀ o, 0 ≤ w o) :
    (Finset.univ.sup' Finset.univ_nonempty fun a => ∑ o, w o * u a o) ≤
      ∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o := by
  apply Finset.sup'_le
  intro a _
  apply Finset.sum_le_sum
  intro o _
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun a => u a o) (Finset.mem_univ a))
    (hw o)

/-- Value of information is zero exactly when a single action is optimal
under every outcome the experiment can actually produce.

The support qualification is the whole content of the statement, and it is
where a careless version goes wrong. Quantifying over *every* outcome, rather
than every outcome of positive weight, makes the criterion false: an outcome of
weight zero contributes nothing to either side, so an action that is optimal
everywhere except there still leaves the value of information at zero, while
the unqualified right-hand side fails. `value_of_information_eq_zero_iff` is
the corollary for strictly positive weights, where the qualification can be
dropped because it is vacuous.

Aristotle reached the same qualification independently, from the informal claim
alone, and produced the two-outcome counterexample that forces it. This project
had the side condition too, but paid for it globally, by assuming every outcome
has positive weight; that assumption is not needed and is dropped here. -/
theorem value_of_information_eq_zero_iff_possible (u : A → O → ℝ) (w : O → ℝ)
    (hw : ∀ o, 0 ≤ w o) :
    (Finset.univ.sup' Finset.univ_nonempty fun a => ∑ o, w o * u a o) =
      (∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o)
    ↔ ∃ a : A, ∀ o, 0 < w o → ∀ a' : A, u a' o ≤ u a o := by
  constructor
  · intro heq
    obtain ⟨a₀, -, ha₀⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A))
        (fun a => ∑ o, w o * u a o)
    have hsum : ∑ o, w o * u a₀ o
        = ∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o := by
      rw [← heq]
      exact ha₀.symm
    have hnonneg : ∀ o ∈ (Finset.univ : Finset O),
        0 ≤ w o * ((Finset.univ.sup' Finset.univ_nonempty fun a => u a o) - u a₀ o) := by
      intro o _
      exact mul_nonneg (hw o)
        (sub_nonneg.mpr (Finset.le_sup' (fun a => u a o) (Finset.mem_univ a₀)))
    have hzero :
        ∑ o, w o * ((Finset.univ.sup' Finset.univ_nonempty fun a => u a o) - u a₀ o) = 0 := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← hsum, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    refine ⟨a₀, fun o hpos a' => ?_⟩
    rcases mul_eq_zero.mp (hterm o (Finset.mem_univ o)) with h | h
    · exact absurd h (ne_of_gt hpos)
    · have hs : (Finset.univ.sup' Finset.univ_nonempty fun a => u a o) = u a₀ o :=
        sub_eq_zero.mp h
      calc u a' o ≤ Finset.univ.sup' Finset.univ_nonempty (fun a => u a o) :=
            Finset.le_sup' (fun a => u a o) (Finset.mem_univ a')
        _ = u a₀ o := hs
  · rintro ⟨a, ha⟩
    have hterms : ∀ o ∈ (Finset.univ : Finset O),
        w o * u a o
          = w o * Finset.univ.sup' Finset.univ_nonempty fun a' => u a' o := by
      intro o _
      rcases eq_or_lt_of_le (hw o) with h | h
      · rw [← h]; ring
      · congr 1
        exact (le_antisymm (Finset.sup'_le _ _ fun a' _ => ha o h a')
          (Finset.le_sup' (fun a' => u a' o) (Finset.mem_univ a))).symm
    refine le_antisymm (value_of_information_nonneg u w hw) ?_
    rw [← Finset.sum_congr rfl hterms]
    exact Finset.le_sup' (fun a => ∑ o, w o * u a o) (Finset.mem_univ a)

/-- Under strictly positive weights, the support-qualified equality criterion
reduces to the existence of one action maximizing utility at every outcome. -/
theorem value_of_information_eq_zero_iff (u : A → O → ℝ) (w : O → ℝ)
    (hw : ∀ o, 0 < w o) :
    (Finset.univ.sup' Finset.univ_nonempty fun a => ∑ o, w o * u a o) =
      (∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o)
    ↔ ∃ a : A, ∀ o, ∀ a' : A, u a' o ≤ u a o := by
  rw [value_of_information_eq_zero_iff_possible u w fun o => (hw o).le]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, fun o a' => ha o (hw o) a'⟩,
         fun ⟨a, ha⟩ => ⟨a, fun o _ a' => ha o a'⟩⟩


end ValueInformation

/-! ## The concept lattice of observation support

For the context of states, observations, and possibility-at, mathlib's
complete lattice of formal concepts records the distinctions induced by the
support of the observation channel. Two states have equal observation support
precisely when no formal concept separates them. -/

section ConceptLattice

variable {S O : Type*}

/-- The observation context of a channel: `o` is possible at `s`. -/
def possibleAt (Z : S → PMF O) (s : S) (o : O) : Prop := Z s o ≠ 0

/-- Support equivalence: the channel cannot tell `s` from `s'` even at the
level of which observations are possible at all. -/
def SupportEquiv (Z : S → PMF O) (s s' : S) : Prop :=
  ∀ o, Z s o ≠ 0 ↔ Z s' o ≠ 0

/-- The object concept of a state: the concept generated by it. -/
def objectConcept (r : S → O → Prop) (s : S) : Concept S O r :=
  ⟨lowerPolar r (upperPolar r {s}), upperPolar r {s},
   upperPolar_lowerPolar_upperPolar r {s}, rfl⟩

theorem mem_objectConcept_self (r : S → O → Prop) (s : S) :
    s ∈ (objectConcept r s).extent :=
  subset_lowerPolar_upperPolar r {s} (Set.mem_singleton s)

/-- States are support-equivalent exactly when no formal concept of the
observation context separates them. -/
theorem supportEquiv_iff_no_concept_separates (Z : S → PMF O) (s s' : S) :
    SupportEquiv Z s s' ↔
      ∀ c : Concept S O (possibleAt Z), s ∈ c.extent ↔ s' ∈ c.extent := by
  constructor
  · intro h c
    have hmem : ∀ x : S, x ∈ c.extent ↔ ∀ ⦃o⦄, o ∈ c.intent → possibleAt Z x o := by
      intro x
      conv_lhs => rw [← c.lowerPolar_intent]
      exact Iff.rfl
    rw [hmem s, hmem s']
    constructor
    · intro hx o ho
      exact (h o).mp (hx ho)
    · intro hx o ho
      exact (h o).mpr (hx ho)
  · intro h o
    have hs' : s' ∈ (objectConcept (possibleAt Z) s).extent :=
      (h _).mp (mem_objectConcept_self _ _)
    have hs : s ∈ (objectConcept (possibleAt Z) s').extent :=
      (h _).mpr (mem_objectConcept_self _ _)
    constructor
    · intro hzs
      exact hs' ((mem_upperPolar_singleton _).mpr hzs)
    · intro hzs'
      exact hs ((mem_upperPolar_singleton _).mpr hzs')

end ConceptLattice

end

end HardProblems


/-! Target module: LeanTest/HardProblems/InformationOrder.lean -/


/-!
# Deterministic information preorder and decision relevance

An observation or representation is modeled here only as a map from states to
reported values. Its information content is the partition of states induced
by equality of reports. Post-processing can merge partition cells but cannot
separate states that the original report identified.

The decision consequence is explicit. An action is robust at the current
report when it is acceptable at every state compatible with that report. A
finer experiment has smaller compatibility classes and therefore weakly more
robust actions. A finite example makes this inclusion strict when a quotient
erases a distinction on which the acceptable action depends.

These are deterministic partition and order results. They do not define
entropy, mutual information, statistical sufficiency, or a stochastic data
processing inequality.
-/

namespace HardProblems
namespace InformationOrder

universe u v w z

/-- States are indistinguishable under an observation map when they produce
the same report. -/
def Indist {S : Type u} {O : Type v} (observe : S → O) (x y : S) : Prop :=
  observe x = observe y

/-- Equality of reports induces an equivalence relation on states. -/
theorem indist_equivalence {S : Type u} {O : Type v} (observe : S → O) :
    Equivalence (Indist observe) where
  refl _ := rfl
  symm h := h.symm
  trans hxy hyz := hxy.trans hyz

/-- `fine` refines `coarse` when the coarse report is obtained by deterministic
post-processing of the fine report. This orients the existing
`HardProblems.FactorsThrough` relation as an information preorder; it does not
introduce a second notion of factorization. -/
def ExperimentRefines {S : Type u} {F : Type v} {C : Type w}
    (fine : S → F) (coarse : S → C) : Prop :=
  FactorsThrough coarse fine

/-- Every experiment refines itself. -/
theorem experimentRefines_refl {S : Type u} {O : Type v}
    (observe : S → O) : ExperimentRefines observe observe := by
  exact ⟨id, by funext x; rfl⟩

/-- Deterministic experiment refinement is transitive. -/
theorem experimentRefines_trans {S : Type u} {A : Type v} {B : Type w}
    {C : Type z} {first : S → A} {second : S → B} {third : S → C}
    (h₁ : ExperimentRefines first second)
    (h₂ : ExperimentRefines second third) :
    ExperimentRefines first third := by
  rcases h₁ with ⟨post₁, rfl⟩
  rcases h₂ with ⟨post₂, rfl⟩
  exact ⟨post₂ ∘ post₁, by funext x; rfl⟩

/-- Refinement reverses inclusion of indistinguishability classes: equality of
fine reports forces equality of coarse reports. -/
theorem ExperimentRefines.indist {S : Type u} {F : Type v} {C : Type w}
    {fine : S → F} {coarse : S → C}
    (h : ExperimentRefines fine coarse) {x y : S}
    (hxy : Indist fine x y) : Indist coarse x y := by
  exact (show FactorsThrough coarse fine from h).eq_of_eq hxy

/-- Actions acceptable at every state compatible with the current report.
The acceptable-action predicate is part of the task, rather than part of the
observation alone. -/
def RobustActions {S : Type u} {O : Type v} {A : Type w}
    (observe : S → O) (Acceptable : S → A → Prop) (x : S) : Set A :=
  {a | ∀ y, Indist observe x y → Acceptable y a}

/-- A finer experiment weakly enlarges the set of robust acceptable actions.
The result is task-relevant but deterministic: it compares compatibility
classes, not probabilities or average information. -/
theorem ExperimentRefines.robustActions_mono
    {S : Type u} {F : Type v} {C : Type w} {A : Type z}
    {fine : S → F} {coarse : S → C}
    (h : ExperimentRefines fine coarse) (Acceptable : S → A → Prop) (x : S) :
    RobustActions coarse Acceptable x ⊆ RobustActions fine Acceptable x := by
  intro a ha y hxy
  exact ha y (h.indist hxy)

/-- Mutual deterministic factorization gives exactly the same induced
indistinguishability relation. The report types and report values themselves
need not be equal. -/
theorem indist_iff_of_mutual_refinement
    {S : Type u} {O₁ : Type v} {O₂ : Type w}
    {first : S → O₁} {second : S → O₂}
    (h₁₂ : ExperimentRefines first second)
    (h₂₁ : ExperimentRefines second first) (x y : S) :
    Indist first x y ↔ Indist second x y :=
  ⟨h₁₂.indist, h₂₁.indist⟩

/-- Mutual deterministic factorization preserves every robust action set for
every task predicate. -/
theorem robustActions_eq_of_mutual_refinement
    {S : Type u} {O₁ : Type v} {O₂ : Type w} {A : Type z}
    {first : S → O₁} {second : S → O₂}
    (h₁₂ : ExperimentRefines first second)
    (h₂₁ : ExperimentRefines second first)
    (Acceptable : S → A → Prop) (x : S) :
    RobustActions first Acceptable x = RobustActions second Acceptable x := by
  apply Set.Subset.antisymm
  · exact h₂₁.robustActions_mono Acceptable x
  · exact h₁₂.robustActions_mono Acceptable x

/-- A strict finite decision loss. The identity experiment separates the two
Bool states, while the quotient to `Unit` merges them. An action is acceptable
exactly when it names the true state. At state `false`, the fine report permits
the robust action `false`; the coarse report permits no robust action. -/
theorem quotient_strict_decision_loss :
    let fine : Bool → Bool := id
    let coarse : Bool → Unit := fun _ ↦ ()
    let Acceptable : Bool → Bool → Prop := fun state action ↦ state = action
    ExperimentRefines fine coarse ∧
      ¬ Indist fine false true ∧ Indist coarse false true ∧
      RobustActions coarse Acceptable false = ∅ ∧
      RobustActions fine Acceptable false = {false} ∧
      RobustActions coarse Acceptable false ⊂
        RobustActions fine Acceptable false := by
  dsimp
  refine ⟨⟨fun _ ↦ (), rfl⟩, by simp [Indist], by simp [Indist], ?_⟩
  have hCoarse : RobustActions (fun _ : Bool ↦ ())
      (fun state action : Bool ↦ state = action) false = ∅ := by
    ext action
    constructor
    · intro ha
      have hFalse := ha false (by rfl)
      have hTrue := ha true (by rfl)
      simp only [Set.mem_empty_iff_false]
      cases action <;> simp_all
    · simp
  have hFine : RobustActions id
      (fun state action : Bool ↦ state = action) false = {false} := by
    ext action
    simp [RobustActions, Indist]
  refine ⟨hCoarse, hFine, ?_⟩
  rw [hCoarse, hFine]
  exact Set.empty_ssubset.mpr (Set.singleton_nonempty false)

end InformationOrder
end HardProblems
