import Mathlib

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


/-! Target module: LeanTest/HardProblems/Dynamics.lean -/


/-!
# Hard Problems, Chapters 4, 5, 8, 9: agency, latency, reflexivity, probes

One file because the four chapters share the same machinery: trajectory
distributions of a controlled Markov step.

Results proved:

* `constrainedReachable_mono_alpha`, `constrainedReachable_mono_goal`:
  chance-constrained reachability behaves monotonically in the risk budget
  and the target set (sanity conditions the book's definition should satisfy,
  and does).
* `AuthorityMap.classify`: the direct/induce/exogenous partition classifies
  every apparent intervention exactly once.
* `no_signal_before_lag`: reviewing strictly before the observability lag
  cannot produce a discriminating signal at resolution `δ`. This is the
  provable core of chapter 5's overcorrection warning.
* `extendStep_fst`: state augmentation. A reflexive system (chapter 8), where
  other agents' policies update in response to actions, is a Markov system on
  the extended state `S × Π₋₀`. The S-marginal of one extended step recovers
  the original kernel.
* `goodhart_witness_example`: a two-line concrete instance of metric-goal
  decoupling under intervention.
* `not_decisionRelevant_iff`: a probe is decision-irrelevant exactly when its
  action recommendation is constant across possible outcomes (chapter 9's
  practical criterion, stated as an iff).
-/

namespace HardProblems

noncomputable section

open scoped ENNReal
open MeasureTheory

variable {S A O P : Type*}

/-! ## Trajectories (chapter 4) -/

/-- Fold a Markov policy and a transition kernel into a closed-loop step. -/
def stepOf (T : S → A → PMF S) (π : S → PMF A) : S → PMF S :=
  fun s => (π s).bind (T s)

/-- Distribution over length-`(n+1)` trajectories (as lists, initial state
first) generated by a step kernel. -/
def rollout (step : S → PMF S) : ℕ → S → PMF (List S)
  | 0, s => PMF.pure [s]
  | n + 1, s => (step s).bind fun s' => (rollout step n s').map (s :: ·)

/-- The chance-constraint event of chapter 4: the trajectory ends in the
target set `Gset` and never leaves the safe set `C`. -/
def SafeGoal (Gset C : Set S) : Set (List S) :=
  {l | (∃ g ∈ Gset, l.getLast? = some g) ∧ ∀ z ∈ l, z ∈ C}

/-- Success probability of a policy for the safe-reachability event. -/
def successProb (T : S → A → PMF S) (π : S → PMF A)
    (Gset C : Set S) (n : ℕ) (s₀ : S) : ℝ≥0∞ :=
  (rollout (stepOf T π) n s₀).toOuterMeasure (SafeGoal Gset C)

/-- Chapter 4's constrained reachability: some admissible policy reaches the
target within horizon `n`, staying safe, with probability at least `1 - α`. -/
def ConstrainedReachable (T : S → A → PMF S) (Pols : Set (S → PMF A))
    (Gset C : Set S) (α : ℝ≥0∞) (n : ℕ) (s₀ : S) : Prop :=
  ∃ π ∈ Pols, 1 - α ≤ successProb T π Gset C n s₀

/-- A larger risk budget can only help. -/
theorem constrainedReachable_mono_alpha
    {T : S → A → PMF S} {Pols : Set (S → PMF A)} {Gset C : Set S}
    {α α' : ℝ≥0∞} {n : ℕ} {s₀ : S} (hα : α ≤ α')
    (h : ConstrainedReachable T Pols Gset C α n s₀) :
    ConstrainedReachable T Pols Gset C α' n s₀ := by
  obtain ⟨π, hπ, hp⟩ := h
  exact ⟨π, hπ, le_trans (tsub_le_tsub_left hα 1) hp⟩

/-- Enlarging the target set can only help. -/
theorem constrainedReachable_mono_goal
    {T : S → A → PMF S} {Pols : Set (S → PMF A)} {Gset Gset' C : Set S}
    {α : ℝ≥0∞} {n : ℕ} {s₀ : S} (hG : Gset ⊆ Gset')
    (h : ConstrainedReachable T Pols Gset C α n s₀) :
    ConstrainedReachable T Pols Gset' C α n s₀ := by
  obtain ⟨π, hπ, hp⟩ := h
  refine ⟨π, hπ, le_trans hp (measure_mono ?_)⟩
  rintro l ⟨⟨g, hg, hlast⟩, hsafe⟩
  exact ⟨⟨g, hG hg, hlast⟩, hsafe⟩

/-- The reversibility coordinate `R` of the hardness profile, as a special
case: recovery is reachability of the acceptable region with the path
constraint switched off. -/
abbrev Recoverable (T : S → A → PMF S) (Pols : Set (S → PMF A))
    (C : Set S) (α : ℝ≥0∞) (n : ℕ) (s₀ : S) : Prop :=
  ConstrainedReachable T Pols C Set.univ α n s₀

/-- Chapter 4's authority map: a partition of apparent interventions into
directly controlled, inducible, and exogenous. -/
structure AuthorityMap (Act : Type*) where
  direct : Set Act
  induce : Set Act
  exogenous : Set Act
  covers : direct ∪ induce ∪ exogenous = Set.univ
  direct_induce : Disjoint direct induce
  direct_exogenous : Disjoint direct exogenous
  induce_exogenous : Disjoint induce exogenous

/-- Every apparent intervention is classified. Combined with the disjointness
fields, the classification is unique: "take ownership" is not a category. -/
theorem AuthorityMap.classify {Act : Type*} (M : AuthorityMap Act) (a : Act) :
    a ∈ M.direct ∨ a ∈ M.induce ∨ a ∈ M.exogenous := by
  have ha : a ∈ M.direct ∪ M.induce ∪ M.exogenous := M.covers ▸ Set.mem_univ a
  simpa [Set.mem_union, or_assoc] using ha

/-- The classification is exclusive as well as total: no intervention lands
in two cells of the authority map (immediate from the map's disjointness
requirements, recorded so that "exactly one" is a stated proposition). -/
theorem AuthorityMap.classify_unique {Act : Type*} (M : AuthorityMap Act) (a : Act) :
    ¬(a ∈ M.direct ∧ a ∈ M.induce) ∧ ¬(a ∈ M.direct ∧ a ∈ M.exogenous) ∧
      ¬(a ∈ M.induce ∧ a ∈ M.exogenous) :=
  ⟨fun ⟨h₁, h₂⟩ => Set.disjoint_left.mp M.direct_induce h₁ h₂,
   fun ⟨h₁, h₂⟩ => Set.disjoint_left.mp M.direct_exogenous h₁ h₂,
   fun ⟨h₁, h₂⟩ => Set.disjoint_left.mp M.induce_exogenous h₁ h₂⟩

/-- The authority map, typed so the category mistake is unrepresentable: a
plan entry classifies as a focal lever (realizing as a focal action `A₀`),
an inducible (realizing as a counterparty action `Aother`), or an exogenous
driver (realizing as an environment input `Ξ`, which is not an action at
all). Because classification is a function into a sum, totality and
exclusivity are theorems rather than axioms, and a driver misfiled as a
lever is a type error rather than a discipline. -/
structure PlanPartition (Entry A₀ Aother Ξ : Type*) where
  classify : Entry → A₀ ⊕ (Aother ⊕ Ξ)

namespace PlanPartition

variable {Entry A₀ Aother Ξ : Type*} (P : PlanPartition Entry A₀ Aother Ξ)

/-- Every plan entry is classified: totality is structural. -/
theorem classify_total (e : Entry) :
    (∃ a, P.classify e = Sum.inl a) ∨ (∃ b, P.classify e = Sum.inr (Sum.inl b)) ∨
      (∃ x, P.classify e = Sum.inr (Sum.inr x)) := by
  rcases h : P.classify e with a | b | x
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact Or.inr (Or.inr ⟨x, rfl⟩)

/-- A driver has no realization as a lever: the category mistake the
untyped map merely legislated against is here impossible to state. -/
theorem driver_not_lever {e : Entry} {x : Ξ}
    (h : P.classify e = Sum.inr (Sum.inr x)) : ¬∃ a, P.classify e = Sum.inl a := by
  rintro ⟨a, ha⟩
  rw [h] at ha
  simp at ha

/-- The typed partition induces the set-based authority map, and the old
structure's axioms (coverage, pairwise disjointness) fall out as theorems:
what had to be assumed of three sets is guaranteed by one function. -/
def toAuthorityMap : AuthorityMap Entry where
  direct := {e | ∃ a, P.classify e = Sum.inl a}
  induce := {e | ∃ b, P.classify e = Sum.inr (Sum.inl b)}
  exogenous := {e | ∃ x, P.classify e = Sum.inr (Sum.inr x)}
  covers := by
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rcases P.classify_total e with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  direct_induce := by
    rw [Set.disjoint_left]
    rintro e ⟨a, ha⟩ ⟨b, hb⟩
    rw [ha] at hb
    simp at hb
  direct_exogenous := by
    rw [Set.disjoint_left]
    rintro e ⟨a, ha⟩ ⟨x, hx⟩
    rw [ha] at hx
    simp at hx
  induce_exogenous := by
    rw [Set.disjoint_left]
    rintro e ⟨b, hb⟩ ⟨x, hx⟩
    rw [hb] at hx
    simp at hx

end PlanPartition

/-! ## Latency (chapter 5)

`obs a n` is the marginal law of the observable at `n` steps after doing `a`;
`dist` is any distributional distance. The book's `τ_δ(a)` leaves the
comparison action implicit; here it is an explicit argument. -/

variable {Ω : Type*}

/-- Observability lag at resolution `δ` between actions `a` and `a'`: the
first time their observable consequences differ by at least `δ`. Equals `⊤`
when the two actions are never `δ`-distinguishable, which is the honest
convention for "this intervention is unobservable at this resolution". -/
def obsLag (dist : Ω → Ω → ℝ≥0∞) (obs : A → ℕ → Ω) (δ : ℝ≥0∞) (a a' : A) : ℕ∞ :=
  sInf {τ : ℕ∞ | ∃ n : ℕ, τ = n ∧ δ ≤ dist (obs a n) (obs a' n)}

/-- Reviewing strictly before the lag yields no discriminating signal: at any
cadence `Δ < τ_δ`, the observable laws under `a` and `a'` are still within
`δ` of each other. Whatever a fast review concludes, it is not evidence that
distinguishes the intervention from its alternative. -/
theorem no_signal_before_lag {dist : Ω → Ω → ℝ≥0∞} {obs : A → ℕ → Ω}
    {δ : ℝ≥0∞} {a a' : A} {Δ : ℕ}
    (h : (Δ : ℕ∞) < obsLag dist obs δ a a') :
    dist (obs a Δ) (obs a' Δ) < δ := by
  by_contra hc
  push Not at hc
  have hmem : (Δ : ℕ∞) ∈ {τ : ℕ∞ | ∃ n : ℕ, τ = n ∧ δ ≤ dist (obs a n) (obs a' n)} :=
    ⟨Δ, rfl, hc⟩
  exact absurd (sInf_le hmem) (not_le.mpr h)

/-- Demanding a stronger signal never shortens the wait: the observability
lag is monotone in the resolution `δ`. (Also proved independently by
Harmonic's Aristotle prover; see `aristotle/`.) -/
theorem obsLag_mono_resolution (dist : Ω → Ω → ℝ≥0∞) (obs : A → ℕ → Ω)
    {δ δ' : ℝ≥0∞} (h : δ ≤ δ') (a a' : A) :
    obsLag dist obs δ a a' ≤ obsLag dist obs δ' a a' := by
  refine sInf_le_sInf ?_
  rintro τ ⟨n, rfl, hn⟩
  exact ⟨n, rfl, h.trans hn⟩

/-- Latency is observability with a clock: the lag against a comparison is
finite exactly when some horizon distinguishes the two actions at
resolution `δ`. An infinite lag is an observability failure for the pair,
which is why the profile's L and O coordinates are one diagnostic. -/
theorem obsLag_ne_top_iff {dist : Ω → Ω → ℝ≥0∞} {obs : A → ℕ → Ω}
    {δ : ℝ≥0∞} {a a' : A} :
    obsLag dist obs δ a a' ≠ ⊤ ↔ ∃ n : ℕ, δ ≤ dist (obs a n) (obs a' n) := by
  rw [obsLag, ne_eq, sInf_eq_top]
  push Not
  constructor
  · rintro ⟨τ, ⟨n, rfl, hn⟩, -⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, ⟨n, rfl, hn⟩, by simp⟩

/-- The triangle law for lags: with a triangle inequality on `dist`, the
lag against `a''` at resolution `δ` is bounded below by the smaller of the
two half-resolution lags through any intermediate comparison `a'`. Waiting
for a strong signal against a far alternative is bounded by half-signals
through any action between them. (Proof found by Harmonic's Aristotle; see
`aristotle/pool/lagtriangle/`.) -/
theorem min_obsLag_le (dist : Ω → Ω → ℝ≥0∞) (obs : A → ℕ → Ω)
    (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (δ : ℝ≥0∞) (a a' a'' : A) :
    min (obsLag dist obs (δ / 2) a a') (obsLag dist obs (δ / 2) a' a'')
      ≤ obsLag dist obs δ a a'' := by
  unfold obsLag
  apply le_sInf
  intro τ hτ
  rcases hτ with ⟨n, rfl, hn⟩
  by_cases h₁ : δ / 2 ≤ dist (obs a n) (obs a' n)
  · exact le_trans (min_le_left _ _) (sInf_le ⟨n, rfl, h₁⟩)
  · have h₂ : δ / 2 ≤ dist (obs a' n) (obs a'' n) := by
      by_contra h₂
      have hadd := ENNReal.add_lt_add (lt_of_not_ge h₁) (lt_of_not_ge h₂)
      rw [ENNReal.add_halves] at hadd
      exact (not_lt_of_ge (hn.trans (htri _ _ _))) hadd
    exact le_trans (min_le_right _ _) (sInf_le ⟨n, rfl, h₂⟩)

/-! ## Reflexivity (chapter 8) -/

/-- One step of a reflexive system: the transition depends on the other
agents' current policy configuration `p : P`, and that configuration adapts
in response to the focal action via `U`. -/
def extendStep (T : S → A → P → PMF S) (U : P → A → P) :
    S × P → A → PMF (S × P) :=
  fun sp a => (T sp.1 a sp.2).map fun s' => (s', U sp.2 a)

/-- State augmentation: the extended system is an ordinary Markov kernel on
`S × P`, and its state marginal recovers the original transition. Reflexivity
is therefore not beyond the formalism; it relocates the state. The cost is
that `P` is typically unobserved, which feeds back into chapter 3. -/
theorem extendStep_fst (T : S → A → P → PMF S) (U : P → A → P)
    (sp : S × P) (a : A) :
    (extendStep T U sp a).map Prod.fst = T sp.1 a sp.2 := by
  simp only [extendStep]
  rw [PMF.map_comp]
  have h : (Prod.fst ∘ fun s' : S => (s', U sp.2 a)) = id := rfl
  rw [h, PMF.map_id]

/-- Stochastic adaptation: the operator returns a distribution over next
policy configurations. Dependence on observations or realized payoffs folds
into the policy coordinate `P` the same way. -/
def extendStepRand (T : S → A → P → PMF S) (U : P → A → PMF P) :
    S × P → A → PMF (S × P) :=
  fun sp a => (T sp.1 a sp.2).bind fun s' => (U sp.2 a).map fun p' => (s', p')

/-- The state marginal of the stochastic augmentation also recovers the
original kernel: randomizing the adaptation does not change the conclusion
of `extendStep_fst`. -/
theorem extendStepRand_fst (T : S → A → P → PMF S) (U : P → A → PMF P)
    (sp : S × P) (a : A) :
    (extendStepRand T U sp a).map Prod.fst = T sp.1 a sp.2 := by
  have h : ∀ s' : S, ((U sp.2 a).map fun _ => s') = PMF.pure s' := by
    intro s'
    exact PMF.map_const _ _
  simp only [extendStepRand, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [h]
  exact PMF.bind_pure _

/-- Governance as dynamics: reading the policy coordinate `P` of
`extendStep` as the current weight vector or decision rule, the governed
system is an ordinary Markov process on the extended state whose
state-marginal recovers the original dynamics. Governance is endogenous as
dynamics; what remains outside, by design, is the legitimacy predicate on
rule updates, which no augmentation converts into a theorem. -/
theorem governedStep_fst (T : S → A → P → PMF S) (U : P → A → P)
    (sp : S × P) (a : A) :
    (extendStep T U sp a).map Prod.fst = T sp.1 a sp.2 :=
  extendStep_fst T U sp a

/-- A Goodhart witness: under the intervened dynamics the metric does not
fall while the goal strictly falls. Existence of a witness refutes the claim
that the metric is intervention-stable. -/
def GoodhartWitness (m g : S → ℝ) (base intervened : S → S) (s : S) : Prop :=
  m (base s) ≤ m (intervened s) ∧ g (intervened s) < g (base s)

/-- A concrete decoupling: metric = first coordinate, goal = second; the
intervention raises the metric and lowers the goal. -/
theorem goodhart_witness_example :
    GoodhartWitness (fun p : ℝ × ℝ => p.1) (fun p => p.2)
      id (fun p => (p.1 + 1, p.2 - 1)) (0, 0) := by
  constructor <;> norm_num

/-! ## Probes (chapter 9) -/

/-- A probe: a set of outcomes considered possible, and the action each
outcome would select. -/
structure Probe (O Act : Type*) where
  possible : Set O
  decide : O → Act

/-- Chapter 9's practical criterion: a probe is decision-relevant when at
least two possible outcomes select different subsequent actions. -/
def DecisionRelevant {Act : Type*} (e : Probe O Act) : Prop :=
  ∃ o₁ ∈ e.possible, ∃ o₂ ∈ e.possible, e.decide o₁ ≠ e.decide o₂

/-- A probe is decision-irrelevant exactly when its recommendation is
constant on the possible outcomes: you were going to do that anyway, so the
experiment purchases no decision-relevant information. -/
theorem not_decisionRelevant_iff {Act : Type*} (e : Probe O Act) :
    ¬DecisionRelevant e ↔
      ∀ o₁ ∈ e.possible, ∀ o₂ ∈ e.possible, e.decide o₁ = e.decide o₂ := by
  unfold DecisionRelevant
  push Not
  rfl

end
end HardProblems
