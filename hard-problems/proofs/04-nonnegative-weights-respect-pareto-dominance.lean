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


/-! Target module: LeanTest/HardProblems/Objectives.lean -/


/-!
# Hard Problems, Chapter 2: formulation

Vector objectives, Pareto structure, scalarization, and the formulation
diagnostics.

Two corrections to the text fall out of the formalization:

* Pareto dominance is a partial order on return *vectors*, but only a
  *preorder* on policies (`policyPreorder`): two distinct policies with equal
  return vectors are equivalent, not equal, so antisymmetry fails.
* "Reverse their ranking under plausible weight vectors" is witnessed
  concretely by `weight_reversal`, and nonnegative scalarization is shown to
  respect Pareto dominance (`scalarize_le_scalarize`,
  `scalarize_lt_scalarize`), so ranking reversals can only occur between
  Pareto-incomparable policies. That is exactly why the choice of weights is
  governance, not mathematics.
-/

namespace HardProblems

variable {k : ℕ}

/-- The space of return vectors `J ∈ ℝ^k`, with the pointwise order. -/
abbrev ReturnVec (k : ℕ) := Fin k → ℝ

/-- Pareto dominance: `u` dominates `v` when `u` is at least as good in every
coordinate and strictly better in some coordinate. This is exactly the strict
order of the pointwise partial order on `ℝ^k`. -/
def ParetoDominates (u v : ReturnVec k) : Prop := v < u

theorem paretoDominates_iff {u v : ReturnVec k} :
    ParetoDominates u v ↔ (∀ i, v i ≤ u i) ∧ ∃ i, v i < u i := by
  simp [ParetoDominates, Pi.lt_def, Pi.le_def]

set_option warn.classDefReducibility false in
/-- Policies are only *preordered* by their return vectors: the pullback of
the pointwise order along `J`. Antisymmetry fails whenever two distinct
policies earn identical returns, so the book's phrase "partially ordered"
should be read as "preordered". -/
def policyPreorder {P : Type*} (J : P → ReturnVec k) : Preorder P :=
  Preorder.lift J

/-- The failure of antisymmetry is witnessed, not merely asserted: two
distinct policies with identical return vectors are equivalent under the
lifted preorder without being equal. (When `J` is injective the lifted
order is a partial order, so the failure is a property of return
equivalence, not of the construction.) -/
theorem policyPreorder_not_antisymmetric :
    ∃ (P : Type) (J : P → ReturnVec 1) (p q : P),
      p ≠ q ∧ (policyPreorder J).le p q ∧ (policyPreorder J).le q p := by
  refine ⟨Bool, fun _ _ => 0, true, false, by decide, ?_, ?_⟩ <;>
    exact le_refl fun _ => (0 : ℝ)

/-- Linear scalarization `w ⋅ J`. -/
def scalarize (w u : ReturnVec k) : ℝ := ∑ i, w i * u i

/-- Nonnegative weights respect weak Pareto improvement. -/
theorem scalarize_le_scalarize {w u v : ReturnVec k}
    (hw : ∀ i, 0 ≤ w i) (h : v ≤ u) :
    scalarize w v ≤ scalarize w u :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

/-- Strictly positive weights respect strict Pareto dominance: a dominated
policy can never win under any strictly positive scalarization. -/
theorem scalarize_lt_scalarize {w u v : ReturnVec k}
    (hw : ∀ i, 0 < w i) (h : ParetoDominates u v) :
    scalarize w v < scalarize w u := by
  obtain ⟨hle, i₀, hlt⟩ := paretoDominates_iff.mp h
  exact Finset.sum_lt_sum
    (fun i _ => mul_le_mul_of_nonneg_left (hle i) (hw i).le)
    ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hw i₀)⟩

end HardProblems
