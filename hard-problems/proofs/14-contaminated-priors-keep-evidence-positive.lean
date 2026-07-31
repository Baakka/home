import LeanTest.HardProblems.Core

/-!
# Hard Problems, Chapter 3: observability

Observational equivalence, decision-critical ambiguity, robust actions, and
the belief-state update.

Results proved here that the chapter asserts or implicitly relies on:

* `obsEquiv_equivalence`: observational equivalence (equality of the
  observation-process law under every probing policy and horizon) is an
  equivalence relation.
* `DecisionCritical.no_robust_action`: under decision-critical ambiguity
  there is no action acceptable across the whole equivalence class, which is
  the precise content of "the agent cannot choose reliably".
* `robustSet_eq_iInter`: a robust action is exactly a member of the
  intersection of acceptable sets over the equivalence class.
* `bayesUpdate`: the canonical belief update. Its well-definedness hypothesis
  `bayesEvidence ≠ 0` is not a technicality: it fails exactly when the
  observation has zero predictive probability under the maintained model,
  which is the moment the model class itself is refuted. The book should say
  this; the review does.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

variable {S A O : Type*}

/-- The law of the focal observation sequence: run the maintained model `M`
for `n` steps from state `s` under a probing policy `π` (a function of the
observation history), returning the distribution over observation histories.
The accumulator `h` carries observations already made.

Timing convention (matching the book's chapter 1 display): each step
observes the current state and then acts, so the emitted sequence is
`o_0 ~ Z(· ∣ s_0), o_1 ~ Z(· ∣ s_1), ...`: an initial observation of the
start state, then one observation of each post-transition state. This is
the same convention the belief update uses, where `bayesUpdate` weights by
the likelihood of the observation at the post-transition state. -/
def obsProcess (M : POSystem S A O) (π : List O → PMF A) :
    ℕ → S → List O → PMF (List O)
  | 0, _, h => PMF.pure h
  | n + 1, s, h =>
    (M.Z s).bind fun o =>
      (π (h ++ [o])).bind fun a =>
        (M.T s a).bind fun s' =>
          obsProcess M π n s' (h ++ [o])

/-- Chapter 3's observational equivalence `s ≡_{0,M} s'`: no admissible
probing policy can distinguish the two states at any finite horizon. -/
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
the equivalence class of `s`. This is the book's third escape route
("choose an action robust across the equivalence class") stated precisely. -/
theorem robustSet_eq_iInter (M : POSystem S A O) (Astar : S → Set A) (s : S) :
    {a | RobustAcceptable M Astar s a} = ⋂ s' ∈ {s' | ObsEquiv M s s'}, Astar s' := by
  ext a
  simp [RobustAcceptable]

/-- Under decision-critical ambiguity no robust action exists: whatever is
acceptable at `s` is forbidden at `s'` and conversely. Probing or model
revision is then forced; no policy choice can dissolve the ambiguity. -/
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

/-- The canonical belief update of chapter 3. The hypothesis `h` is the real
content: Bayes' rule is undefined exactly when the observation was impossible
under every state the maintained model deems reachable, and that event should
trigger model-class revision, not a numerical exception. -/
def bayesUpdate (h : bayesEvidence b step Z o ≠ 0) : PMF S :=
  PMF.normalize (fun s' => Z s' o * (b.bind step) s') h
    (lt_of_le_of_lt (bayesEvidence_le_one b step Z o) ENNReal.one_lt_top).ne

/-- The posterior is the likelihood-times-prediction, renormalized. -/
theorem bayesUpdate_apply (h : bayesEvidence b step Z o ≠ 0) (s' : S) :
    bayesUpdate b step Z o h s' =
      Z s' o * (b.bind step) s' * (bayesEvidence b step Z o)⁻¹ :=
  rfl

/-- The belief update extended by a default: when the observation has zero
predictive probability the maintained model is refuted (see `bayesUpdate`),
and we conservatively keep the prediction. The martingale theorem below does
not depend on the choice of default. -/
noncomputable def bayesUpdateOr : PMF S :=
  if h : bayesEvidence b step Z o ≠ 0 then bayesUpdate b step Z o h
  else b.bind step

/-- Total probability, the martingale property of Bayesian updating: the
posterior, averaged over the predictive law of the observation, is exactly
the prediction. Updating on evidence redistributes belief; it cannot
manufacture information the observation channel did not carry. In the
book's terms, this is the sanity bound on chapter 3's escape routes: no
choice of dashboard can move the expected belief, only observations that
actually discriminate can. -/
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
predictive law, then update. This closes the chapter 3 to chapter 4 bridge:
beliefs evolve as an ordinary Markov process on the space `PMF S`. -/
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

/-! ## When the class dies: misspecification, localized and prevented

A zero normalizer refutes the model class (see `bayesUpdate`). The two
theorems here turn that event into procedure: the localization says
*where* the class broke (every state the prediction reaches makes the
observation impossible), and the hygiene theorem says a class carrying an
ε-contamination component with full support can never die, only raise an
alarm, the mass flowing to the contamination component. Generating a
substantive successor class remains abduction; what the formalism supplies
is the necessary condition on any successor and the pointer to the broken
support. -/

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

/-- The hygiene: under an ε-contaminated observation model whose
contamination has full support, the evidence is positive for every
observation, from every belief. Bayes cannot die inside the contaminated
class; it can only raise the alarm. -/
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
