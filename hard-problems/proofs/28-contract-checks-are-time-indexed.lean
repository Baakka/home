import Mathlib

/-!
This snippet is about:

  SemanticDrift
  contract_check_time_indexed

found at line 997 of 1005, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Inlined dependency: LeanTest/HardProblems/Core.lean -/


/-!
# Hard Problems, Chapters 1 and 10: the problem object and the navigation contract

Formalization of the mathematical core of the book draft
"Hard Problems: Compositional Navigation in Open, Partially Observable, Adaptive Systems".

Design choices, recorded once and referenced from the review:

* Probability is represented with `PMF` (countably supported distributions).
  The book allows general measurable spaces; everything here generalizes to
  `ProbabilityTheory.Kernel` at the price of measurability side conditions that
  would obscure the decision-theoretic content. This matches the book's own
  remark in section 0 about finite-dimensional notation.
* The model class `Θ` is a fixed unknown parameter type. The book writes a
  time-indexed `θ_t`; see the review (finding on section 1) for why the two
  readings, epistemic uncertainty versus drift, should be separated.
* Policies are typed on observation histories. The book's admissible action
  sets `A_i(s)` depend on the unobserved state, which a history-typed policy
  cannot check; the review flags this as a gap in the text.
-/

namespace HardProblems

set_option linter.checkUnivs false in
/-- Chapter 1: the hard-problem instance
`P = (S, {A_i}, {O_i, Z_i}, T_θ, {G_i}, C, {Π_i}, Θ)`. -/
structure Problem where
  /-- state space `S` -/
  S : Type*
  /-- agent index set `N`; `focal` plays the book's role of agent `0` -/
  Agent : Type*
  focal : Agent
  /-- per-agent action types -/
  Act : Agent → Type*
  /-- admissible actions `A_i(s)`; note the dependence on the unobserved state -/
  adm : ∀ i, S → Set (Act i)
  /-- per-agent observation spaces `O_i` -/
  Obs : Agent → Type*
  /-- the model class `Θ`: epistemic uncertainty over kernels -/
  Model : Type*
  /-- observation kernels `Z_{i,θ}(o_i ∣ s)` -/
  Z : Model → ∀ i, S → PMF (Obs i)
  /-- transition kernel `T_θ(s' ∣ s, a)`, on joint actions -/
  T : Model → S → (∀ i, Act i) → PMF S
  /-- number of objective coordinates `k` -/
  k : ℕ
  /-- vector objective `G : S → ℝ^k` (chapter 2) -/
  G : S → Fin k → ℝ
  /-- per-agent payoffs `G_i`: the realized rewards `r_i` that drive
  adaptation in chapter 8. The focal agent's own objective is the
  vector-valued `G` above; nothing requires the non-focal `G_i` to be known
  to the focal agent. -/
  payoff : Agent → S → ℝ
  /-- safe or feasible set `C ⊆ S` -/
  C : Set S
  /-- policy classes `Π_i`, as observation-history policies -/
  Pol : ∀ i, Set (List (Obs i) → PMF (Act i))

/-- A maintained focal-view model `M = (θ, π₋₀)` (chapter 3). The other agents'
reactions are folded into single-agent kernels. This folding is sound only when
the non-focal policies are Markov in the current state; the review discusses
what breaks otherwise (their internal histories become hidden confounders). -/
structure POSystem (S A O : Type*) where
  /-- marginalized transition kernel `T_{θ,π₋₀}(s' ∣ s, a₀)` -/
  T : S → A → PMF S
  /-- focal observation kernel `Z_{0,θ}(o ∣ s)` -/
  Z : S → PMF O

/-- Chapter 1.1: the hardness profile `H(P) = (F, O, A, L, Ru, Re, X)`.
Each coordinate is a diagnostic claim (a proposition to be argued from
evidence), not a score. Ruggedness lives on the configuration graph and
evaluation of `Ruggedness.lean`; reversibility is recovery reachability in
the sense of `Dynamics.lean`'s `Recoverable`. -/
structure HardnessProfile where
  formulation : Prop
  observability : Prop
  agency : Prop
  latency : Prop
  ruggedness : Prop
  reversibility : Prop
  reflexivity : Prop

/-- The profile's index. The named tuple above is presentation; the
underlying object is an indexed family of diagnostic claims, so extending
the profile means adding an index point, not changing an arity. The
coordinates are moreover not primitive: agency, reversibility, and
ruggedness are one diagnostic (constrained reachability) evaluated at three
re-descriptions of the problem, latency is observability with a clock
(`obsLag_ne_top_iff`), and reflexivity is observability plus agency on the
augmented system (`extendStep_fst`). Formulation alone resists absorption:
it is governance, prior to the system. -/
inductive HardnessCoord where
  | formulation
  | observability
  | agency
  | latency
  | ruggedness
  | reversibility
  | reflexivity
deriving DecidableEq, Repr

/-- The tuple is exactly the evaluation of an indexed family: the profile
carries no structure beyond its index. -/
def HardnessProfile.equivFn : HardnessProfile ≃ (HardnessCoord → Prop) where
  toFun p c :=
    match c with
    | .formulation => p.formulation
    | .observability => p.observability
    | .agency => p.agency
    | .latency => p.latency
    | .ruggedness => p.ruggedness
    | .reversibility => p.reversibility
    | .reflexivity => p.reflexivity
  invFun f :=
    ⟨f .formulation, f .observability, f .agency, f .latency, f .ruggedness,
     f .reversibility, f .reflexivity⟩
  left_inv p := rfl
  right_inv f := by
    funext c
    cases c <;> rfl

/-- The knowns/unknowns matrix as a projection of the profile: a cell
records only whether the destination is settled (formulation) and whether
the current state is estimable (observability). The matrix is an on-ramp,
not a measure; the two theorems below make that precise. -/
def matrixCell (p : HardnessProfile) : Prop × Prop :=
  (p.formulation, p.observability)

/-- The matrix cell does not determine the problem: two profiles can share
a cell and differ in the remaining coordinates. -/
theorem matrixCell_not_injective :
    ∃ p q : HardnessProfile, matrixCell p = matrixCell q ∧ p ≠ q := by
  refine ⟨⟨True, True, True, True, True, True, True⟩,
    ⟨True, True, True, True, False, True, True⟩, rfl, fun h => ?_⟩
  have hru : True = False := congrArg HardnessProfile.ruggedness h
  exact hru ▸ trivial

/-- Every cell is fat: any combination of the five remaining diagnostics
occurs inside any given cell. A "known to known" problem can still be
arbitrarily rugged, laggy, irreversible, and reflexive; the cell says where
to start looking, not what will be found. -/
theorem matrixCell_fiber_fat (f o a l ru re x : Prop) :
    ∃ p : HardnessProfile, matrixCell p = (f, o) ∧ p.agency = a ∧
      p.latency = l ∧ p.ruggedness = ru ∧ p.reversibility = re ∧
      p.reflexivity = x :=
  ⟨⟨f, o, a, l, ru, re, x⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- One row of the model ledger of chapter 1.1. The fields are documentation
data, not mathematics: the point of the ledger is auditability. -/
structure LedgerEntry where
  assumption : String
  evidence : String
  competingModels : String
  damageIfWrong : String
  nextObservation : String

/-- The model ledger: every load-bearing assumption gets a row. -/
abbrev ModelLedger := List LedgerEntry

/-! ## Chapter 10: the stopping rule

The book lists four terminal conditions: execute, probe, escalate, exit.
As stated they are not mutually exclusive (a problem can be feasible for the
focal agent while the objective choice belongs to another authority), so a
deterministic stopping rule needs a priority order. We encode the natural one
and prove the characterizations, which makes the exclusivity explicit. -/

/-- The four verdicts of the chapter 10 stopping rule. -/
inductive Verdict where
  | execute
  | probe
  | escalate
  | infeasible
deriving DecidableEq, Repr

/-- The three findings the stopping rule branches on. -/
structure Assessment where
  /-- a policy is feasible and robust enough under the stated model class -/
  feasibleRobust : Bool
  /-- uncertainty is decision-critical but reducible within constraints -/
  reducibleCriticalUncertainty : Bool
  /-- the required action or objective choice belongs to a different authority -/
  authorityElsewhere : Bool

/-- The stopping rule, with the priority order execute > probe > escalate.
`infeasible` is the residual verdict. -/
def Assessment.verdict (a : Assessment) : Verdict :=
  if a.feasibleRobust then .execute
  else if a.reducibleCriticalUncertainty then .probe
  else if a.authorityElsewhere then .escalate
  else .infeasible

@[simp] theorem Assessment.verdict_execute_iff (a : Assessment) :
    a.verdict = .execute ↔ a.feasibleRobust = true := by
  unfold Assessment.verdict
  split_ifs <;> simp_all

/-- Infeasibility is exactly the failure of all three positive findings:
the rule never declares infeasibility while a live option remains. -/
theorem Assessment.verdict_infeasible_iff (a : Assessment) :
    a.verdict = .infeasible ↔
      a.feasibleRobust = false ∧ a.reducibleCriticalUncertainty = false ∧
        a.authorityElsewhere = false := by
  unfold Assessment.verdict
  split_ifs <;> simp_all

/-! The stopping rule, generalized: chapter 10 notes that the priority
order is itself a governance choice. `verdictOfList` is the rule for an
arbitrary declared order (an ordered list of findings paired with
verdicts, and a residual), and the two theorems are what any such rule
owes its users. (Proofs found by Harmonic's Aristotle; see
`aristotle/pool/verdict/`.) -/

/-- A stopping rule as an ordered list of findings paired with verdicts,
and a residual verdict when nothing fires: first match wins. -/
def verdictOfList {V : Type*} (rules : List (Bool × V)) (residual : V) : V :=
  match rules with
  | [] => residual
  | (b, v) :: rest => if b then v else verdictOfList rest residual

/-- The residual is declared exactly when every finding is negative
(provided no rule reuses the residual verdict): the rule never declares
infeasibility while a live option remains, for any declared order. -/
theorem verdictOfList_eq_residual_iff {V : Type*} (rules : List (Bool × V))
    (residual : V) (hres : ∀ p ∈ rules, p.2 ≠ residual) :
    verdictOfList rules residual = residual ↔ ∀ p ∈ rules, p.1 = false := by
  induction rules with
  | nil => simp [verdictOfList]
  | cons p rest ih =>
    rcases p with ⟨b, v⟩
    cases b <;> simp_all [verdictOfList]

/-- The first firing finding decides, whatever follows it: priority orders
mean what they say. -/
theorem verdictOfList_first_true {V : Type*} (rules₁ rules₂ : List (Bool × V))
    (v : V) (residual : V) (h₁ : ∀ p ∈ rules₁, p.1 = false) :
    verdictOfList (rules₁ ++ (true, v) :: rules₂) residual = v := by
  induction rules₁ with
  | nil => simp [verdictOfList]
  | cons p rest ih =>
    rcases p with ⟨b, w⟩
    simp_all [verdictOfList]

/-- Chapter 11's declared legitimacy-first order, stated in full as an
instance of the general rule: escalate over probe over execute, with
infeasibility residual. -/
def Assessment.legitimacyFirstVerdict (a : Assessment) : Verdict :=
  verdictOfList
    [(a.authorityElsewhere, .escalate),
     (a.reducibleCriticalUncertainty, .probe),
     (a.feasibleRobust, .execute)] .infeasible

/-- Under the legitimacy-first order too, infeasibility is residual: it is
declared only when all three positive findings fail. Inherited from the
general characterization, as any declared order's guarantee should be. -/
theorem Assessment.legitimacyFirst_infeasible_iff (a : Assessment) :
    a.legitimacyFirstVerdict = .infeasible ↔
      a.authorityElsewhere = false ∧ a.reducibleCriticalUncertainty = false ∧
        a.feasibleRobust = false := by
  rw [Assessment.legitimacyFirstVerdict, verdictOfList_eq_residual_iff]
  · simp
  · intro p hp
    fin_cases hp <;> simp

/-- Escalation genuinely outranks everything under the declared order: if
the authority finding fires, the verdict is escalation regardless of the
other findings. -/
theorem Assessment.legitimacyFirst_escalate (a : Assessment)
    (h : a.authorityElsewhere = true) :
    a.legitimacyFirstVerdict = .escalate := by
  have := verdictOfList_first_true ([] : List (Bool × Verdict))
    [(a.reducibleCriticalUncertainty, .probe), (a.feasibleRobust, .execute)]
    Verdict.escalate Verdict.infeasible (by simp)
  simpa [Assessment.legitimacyFirstVerdict, h] using this

/-- Chapter 10: the navigation contract
`N = (Ĝ, b̂ₜ, Â, τ̂, Ĉ, Π̂, e, σ)`. Fields follow the book's order; the
mathematical content of each hat lives in the corresponding chapter file. -/
structure NavigationContract (S A E : Type*) where
  /-- `Ĝ`: current objective specification and unresolved trade-offs -/
  objectiveSpec : String
  /-- `b̂ₜ`: current state estimate, if one is maintained -/
  belief : Option (PMF S)
  /-- `Â`: admissible actions currently owned by the focal agent -/
  admissible : Set A
  /-- `τ̂`: forecast feedback lag bound (⊤ means no forecast) -/
  feedbackLag : ℕ∞
  /-- `Ĉ`: guardrails, as a set the trajectory must not leave -/
  guardrails : Set S
  /-- `Π̂`: anticipated adaptations, recorded for audit -/
  anticipatedAdaptations : String
  /-- `e`: the next decision-relevant probe, if any -/
  nextProbe : Option E
  /-- `σ`: the stopping verdict currently in force -/
  stopping : Verdict

end HardProblems


/-! Inlined dependency: LeanTest/HardProblems/Observability.lean -/


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


/-! Target module: LeanTest/HardProblems/SystemsTheory.lean -/


/-!
# Hard Problems: the systems-theory inheritance, formalized

The book draws on cybernetics and complexity theory. This file formalizes
the pieces of that inheritance that are actually theorems, in the book's own
vocabulary:

* `requisite_variety` (Ashby): a regulator that uses few distinct responses
  cannot confine many distinguishable disturbances to a small outcome set.
  The counting form: |D| is at most (responses used) times (outcomes hit).
* `PassivelyDistinguishable` / `ProbeDistinguishable` (Snowden's
  complicated/complex boundary, made precise): some model classes can be
  separated by watching, others only by acting. `passively_imp_probe` gives
  the easy inclusion; the strict separation witness shows the "complex"
  regime is nonempty, so probe-sense-respond is sometimes the only mode of
  learning.
* `statistic_based_rule_fails` (Campbell, Goodhart): a decision rule that
  acts only through a summary statistic inherits the statistic's blindness.
* `invariance_comp` / `increment_bound_not_compositional` (Leveson):
  set-invariance safety composes; margin-style safety does not. Safety is a
  property of the composition, not of the components.
* `value_of_information_nonneg` (Raiffa): observing before acting never
  lowers the achievable expected utility.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

/-! ## Requisite variety (Ashby) -/

section Ashby

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

/-- Ashby's law of requisite variety, counting form. `ω d a` is the outcome
of disturbance `d` under regulator response `a`. If the response rule `ρ`
separates the disturbances it answers alike (`FiberSeparating`), then the
number of disturbances is at most the number of responses actually used times
the number of outcomes actually hit. Only variety in the regulator can absorb
variety in the disturbances. -/
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

end Ashby

/-! ## Probe identifiability (the complicated/complex boundary) -/

section Cynefin

variable {S A O : Type*}

/-- Two maintained models are passively distinguishable from `s` when the
law of the observation process differs under the constant "null action"
policy `a₀`: watching, without intervening, eventually separates them. -/
def PassivelyDistinguishable (M₁ M₂ : POSystem S A O) (a₀ : A) (s : S) : Prop :=
  ∃ n, obsProcess M₁ (fun _ => PMF.pure a₀) n s [] ≠
        obsProcess M₂ (fun _ => PMF.pure a₀) n s []

/-- Two maintained models are probe distinguishable from `s` when some
admissible policy separates their observation laws. -/
def ProbeDistinguishable (M₁ M₂ : POSystem S A O) (s : S) : Prop :=
  ∃ (π : List O → PMF A) (n : ℕ),
    obsProcess M₁ π n s [] ≠ obsProcess M₂ π n s []

/-- Watching is a special case of acting. -/
theorem passively_imp_probe {M₁ M₂ : POSystem S A O} {a₀ : A} {s : S}
    (h : PassivelyDistinguishable M₁ M₂ a₀ s) : ProbeDistinguishable M₁ M₂ s :=
  let ⟨n, hn⟩ := h
  ⟨fun _ => PMF.pure a₀, n, hn⟩

/-- If two models agree on the observation kernel and on the transition
kernel at the null action, no amount of passive watching separates them,
at any horizon, from any state. -/
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

/-- The complex regime exists: two models over Bool states/actions/observations
that agree under the passive action (false) at every horizon, yet are separated
by the probing action (true). Learning here requires acting. -/
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

end Cynefin

/-! ## Statistic-based rules (Campbell, Goodhart) -/

section Campbell

variable {S A : Type*}

/-- A decision rule that acts only through a summary statistic inherits the
statistic's blindness: if the statistic fails to separate two states whose
acceptable-action sets are disjoint, then every rule based on it acts
unacceptably in at least one of the two. Managing to the dashboard is safe
exactly to the extent that the dashboard separates decision-relevant
states. -/
theorem statistic_based_rule_fails {m : S → ℝ} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : ℝ → A) :
    α (m s) ∉ Astar s ∨ α (m s') ∉ Astar s' := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  rw [hm] at h1
  exact Set.disjoint_left.mp hdisj h1 h2

/-- The statistic-blindness theorem with an arbitrary statistic codomain:
nothing in the argument uses the real numbers. This is the form the
relativization barrier of complexity theory instantiates: a proof
technique whose verdict factors through relativizing observations takes
the same value in the two Baker-Gill-Solovay worlds, whose correct
conclusions are disjoint, so no such technique is correct in both. -/
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

/-- Dashboard form of the general probability-measure obstruction. -/
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

end Campbell

/-! ## Safety and composition (Leveson) -/

section Leveson

/-- Set-invariance safety is compositional: if each component maps the safe
set into itself, so does the composite. This is the kind of safety property
chapter 7's interfaces can carry. -/
theorem invariance_comp {S : Type*} {C : Set S} {f g : S → S}
    (hf : Set.MapsTo f C C) (hg : Set.MapsTo g C C) :
    Set.MapsTo (g ∘ f) C C :=
  hg.comp hf

/-- Margin-style safety is not compositional: two components that each move
the state by at most one can jointly move it by two. Component-level safety
margins do not add up to system-level safety; the hazard lives in the
composition, which is Leveson's point in miniature. -/
theorem increment_bound_not_compositional :
    ∃ f g : ℝ → ℝ,
      (∀ x, |f x - x| ≤ 1) ∧ (∀ x, |g x - x| ≤ 1) ∧
      ∃ x : ℝ, ¬ (|(g ∘ f) x - x| ≤ 1) := by
  refine ⟨fun x => x + 1, fun x => x + 1, fun x => by norm_num,
    fun x => by norm_num, 0, ?_⟩
  norm_num [Function.comp]

/-- The policy space over a finite problem is exponentially large: the
augmentation of chapter 8 is a diagnostic classification, not a computable
space, and this is the one-line reason. -/
theorem card_policySpace (S A : Type*) [Fintype S] [Fintype A] [DecidableEq S] :
    Fintype.card (S → A) = Fintype.card A ^ Fintype.card S :=
  Fintype.card_fun

/-- Reflexivity is expensive, as a counting bound: perfectly regulating the
augmented state of chapter 8 (system state paired with the counterparty's
policy) demands response variety at least `|S| * |A| ^ |S|`. Composing the
requisite-variety bound with the policy-space cardinality turns the
adjective "explosive" into arithmetic. -/
theorem requisite_variety_augmented {S A R O : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq R] [DecidableEq O]
    (ω : S × (S → A) → R → O) (ρ : S × (S → A) → R)
    (hsep : FiberSeparating ω ρ) (o₀ : O) (hperf : ∀ d, ω d (ρ d) = o₀) :
    Fintype.card S * Fintype.card A ^ Fintype.card S ≤
      (Finset.univ.image ρ).card := by
  have h := requisite_variety_perfect ω ρ hsep o₀ hperf
  rwa [Fintype.card_prod, card_policySpace] at h

/-- Semantic drift: the syntax is fixed while its interpretation changes
over time. The wiring of chapter 7 is the constant part; chapter 8's
counter-moves act on the semantics family. -/
def SemanticDrift {W B : Type*} (sem : ℕ → W → B) : Prop :=
  ∃ t x, sem (t + 1) x ≠ sem t x

/-- A contract check is a time-indexed claim: a concrete witness where the
contract holds under the semantics at time zero, the semantics drifts with
the syntax unchanged, and the same contract fails at time one. Checking the
square once certifies the interface only for the moment of checking. -/
theorem contract_check_time_indexed :
    ∃ (sem : ℕ → Bool → Bool) (contract : (Bool → Bool) → Prop),
      contract (sem 0) ∧ SemanticDrift sem ∧ ¬contract (sem 1) := by
  refine ⟨fun t => if t = 0 then id else not, fun f => f true = true, ?_, ⟨0, true, ?_⟩, ?_⟩
  · simp
  · simp
  · simp

end Leveson
end
end HardProblems
