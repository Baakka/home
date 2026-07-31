import Mathlib

/-!
This snippet is about:

  exists_escape_hatch
  Reflects

found at line 493 of 496, near the end of this file.

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


/-! Target module: LeanTest/HardProblems/Ruggedness.lean -/


/-!
# Hard Problems, Chapter 6: ruggedness

The landscape metaphor made literal: a directed graph of feasible policy
configurations, a scalar evaluation, local maxima, and barrier heights.

Results proved:

* `exists_dip_of_barrier_pos`: if the barrier from `x` to `y` is positive
  then *every* admissible path from `x` to `y` passes through a configuration
  strictly worse than `x`. This is exactly the sentence the book asserts
  after the definition, and it is what licenses the phrase "crossing the
  valley" (once mechanism, depth, duration, signal, guardrail, and
  distribution have been contracted separately).
* `barrier_eq_top_of_no_path`: when no admissible path exists at all, the
  barrier is `⊤`. Unreachability and high barriers are different diagnoses
  (chapter 4 versus chapter 6), and the convention keeps them distinguishable.
-/

namespace HardProblems

open scoped ENNReal

variable {X : Type*}

/-- An admissible path in the configuration graph `Adj`, from `x` to `y`,
recorded as its list of visited configurations. -/
structure PathBetween (Adj : X → X → Prop) (x y : X) where
  points : List X
  head_eq : points.head? = some x
  last_eq : points.getLast? = some y
  admissible : points.IsChain Adj

/-- A weak local maximum: no single admissible change improves `J`. -/
def IsLocalMax (Adj : X → X → Prop) (J : X → ℝ) (x : X) : Prop :=
  ∀ y, Adj x y → J y ≤ J x

/-- Barrier height from `x` to `y`: the least, over admissible paths, of the
deepest dip below `J x` along the path (dips measured in `ℝ≥0∞`, so paths
that never dip contribute `0`). Empty infimum is `⊤`: no path, infinite
barrier. -/
noncomputable def barrier (Adj : X → X → Prop) (J : X → ℝ) (x y : X) : ℝ≥0∞ :=
  ⨅ γ : PathBetween Adj x y, ⨆ z ∈ γ.points, ENNReal.ofReal (J x - J z)

/-- A positive barrier means every admissible route to `y` first visits a
configuration strictly worse than the start. This is the formal content of
"every feasible route to the better state first passes through a
lower-valued state". -/
theorem exists_dip_of_barrier_pos {Adj : X → X → Prop} {J : X → ℝ} {x y : X}
    (h : 0 < barrier Adj J x y) (γ : PathBetween Adj x y) :
    ∃ z ∈ γ.points, J z < J x := by
  have hγ : 0 < ⨆ z ∈ γ.points, ENNReal.ofReal (J x - J z) :=
    lt_of_lt_of_le h (iInf_le _ γ)
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp hγ
  obtain ⟨hmem, hpos⟩ := lt_iSup_iff.mp hz
  refine ⟨z, hmem, ?_⟩
  have := ENNReal.ofReal_pos.mp hpos
  linarith

/-- No admissible path at all makes the barrier infinite: an agency problem
(chapter 4), not a ruggedness problem. -/
theorem barrier_eq_top_of_no_path {Adj : X → X → Prop} {J : X → ℝ} {x y : X}
    (h : IsEmpty (PathBetween Adj x y)) :
    barrier Adj J x y = ⊤ :=
  iInf_of_empty _

/-- If some admissible path never dips below the start value, the barrier
vanishes: the converse companion to `exists_dip_of_barrier_pos`. (Also
proved independently by Harmonic's Aristotle prover; see `aristotle/`.) -/
theorem barrier_eq_zero_of_monotone_path {Adj : X → X → Prop} {J : X → ℝ}
    {x y : X} (γ : PathBetween Adj x y) (hγ : ∀ z ∈ γ.points, J x ≤ J z) :
    barrier Adj J x y = 0 := by
  refine le_antisymm ?_ zero_le
  refine le_trans (iInf_le _ γ) ?_
  refine iSup_le fun z => iSup_le fun hz => ?_
  simp [ENNReal.ofReal_eq_zero, hγ z hz]

/-! ### Ruggedness is constrained reachability

The unification behind the hardness profile's index view (chapter 1.1): the
barrier sits below a depth exactly when the target is reachable through the
corresponding superlevel region. Chapter 6's diagnostic is chapter 4's,
evaluated in configuration space. -/

/-- A supremum of `ENNReal`-valued quantities indexed by membership in a
`List` is strictly below a positive bound as soon as each member is. -/
theorem biSup_list_lt {Y : Type*} (f : Y → ℝ≥0∞) {d : ℝ≥0∞} (hd : 0 < d) :
    ∀ l : List Y, (∀ z ∈ l, f z < d) → (⨆ z ∈ l, f z) < d := by
  intro l
  induction l with
  | nil => intro _; simpa using hd
  | cons a t ih =>
      intro h
      rw [show (⨆ z ∈ (a :: t), f z) = f a ⊔ ⨆ z ∈ t, f z by
        simp [List.mem_cons, iSup_or, iSup_sup_eq]]
      exact sup_lt_iff.2 ⟨h a (by simp), ih fun z hz => h z (by simp [hz])⟩

/-- The barrier sits strictly below `d` exactly when some admissible path
keeps every dip strictly below `d`. The backward direction uses the
finiteness of a path's point list: finitely many quantities each below `d`
have supremum below `d`. -/
theorem barrier_lt_iff {Adj : X → X → Prop} {J : X → ℝ} {x y : X}
    {d : ℝ≥0∞} :
    barrier Adj J x y < d ↔
      ∃ γ : PathBetween Adj x y, ∀ z ∈ γ.points,
        ENNReal.ofReal (J x - J z) < d := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 h
    exact ⟨γ, fun z hz =>
      lt_of_le_of_lt (le_biSup (fun z => ENNReal.ofReal (J x - J z)) hz) hγ⟩
  · rintro ⟨γ, hγ⟩
    have hx : x ∈ γ.points := List.mem_of_mem_head? γ.head_eq
    have hd : 0 < d := lt_of_le_of_lt zero_le (hγ x hx)
    exact lt_of_le_of_lt (iInf_le _ γ) (biSup_list_lt _ hd γ.points hγ)

/-! ### Ontological revision: re-description moves barriers

Chapter 7's functors are escape hatches from a configuration space where
the target is unreachable. Three facts pin down when that works: an
admissibility-respecting re-description transfers reachability forward
(so emptiness in the image refutes the technique class at the source,
which is the schema of the complexity-theoretic barrier results); escape
hatches exist (a barrier can be infinite in one representation and zero
in another, so unreachability is a property of the representation); and
an escape is sound only when the re-description reflects the goal. -/

/-- A re-description that respects admissibility maps paths to paths. -/
def PathBetween.map {X X' : Type*} {Adj : X → X → Prop}
    {Adj' : X' → X' → Prop} (φ : X → X')
    (hφ : ∀ {a b}, Adj a b → Adj' (φ a) (φ b)) {x y : X}
    (γ : PathBetween Adj x y) : PathBetween Adj' (φ x) (φ y) where
  points := γ.points.map φ
  head_eq := by rw [List.head?_map, γ.head_eq]; rfl
  last_eq := by rw [List.getLast?_map, γ.last_eq]; rfl
  admissible := (List.isChain_map φ).mpr (γ.admissible.imp fun _ _ h => hφ h)

/-- The schema of the barrier results: if the re-described target is
unreachable, no admissible route existed at the source either, for any
admissibility-respecting re-description. Oracle worlds instantiate this:
emptiness in the image kills the technique class upstairs. -/
theorem isEmpty_of_map_isEmpty {X X' : Type*} {Adj : X → X → Prop}
    {Adj' : X' → X' → Prop} (φ : X → X')
    (hφ : ∀ {a b}, Adj a b → Adj' (φ a) (φ b)) {x y : X}
    (h : IsEmpty (PathBetween Adj' (φ x) (φ y))) :
    IsEmpty (PathBetween Adj x y) :=
  ⟨fun γ => h.false (γ.map φ hφ)⟩

/-- Escape hatches exist: the same start, target, and evaluation can carry
an infinite barrier in one representation and a zero barrier in another.
Unreachability is a property of the representation, not of the problem. -/
theorem exists_escape_hatch :
    ∃ (Adj Adj' : Bool → Bool → Prop) (J : Bool → ℝ),
      barrier Adj J false true = ⊤ ∧ barrier Adj' J false true = 0 := by
  refine ⟨fun _ _ => False, fun _ _ => True, fun _ => 0, ?_, ?_⟩
  · apply barrier_eq_top_of_no_path
    constructor
    rintro ⟨pts, hh, hl, hc⟩
    match pts, hh, hl, hc with
    | [a], hh, hl, _ =>
      simp only [List.head?_cons, Option.some_inj] at hh
      simp only [List.getLast?_singleton, Option.some_inj] at hl
      rw [hh] at hl
      exact Bool.false_ne_true hl
    | a :: b :: t, _, _, hc =>
      exact (List.isChain_cons.mp hc).1 b (by simp)
  · exact barrier_eq_zero_of_monotone_path
      ⟨[false, true], rfl, rfl, by simp [List.isChain_cons]⟩
      (fun z _ => le_rfl)

/-- A re-description is an escape hatch only when it reflects the goal:
success in the image must imply success at the source. Without
reflection, solving the re-described problem proves nothing about the
original. -/
def Reflects {X X' : Type*} (φ : X → X') (P : X → Prop) (P' : X' → Prop) : Prop :=
  ∀ x, P' (φ x) → P x

end HardProblems
