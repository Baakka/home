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

end HardProblems
