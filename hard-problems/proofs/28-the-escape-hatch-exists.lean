import LeanTest.HardProblems.Core

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
