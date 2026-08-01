import Mathlib

/-!
This snippet is about:

  PathBetween
  barrier
  exists_dip_of_barrier_pos
  barrier_eq_top_of_no_path
  barrier_eq_zero_of_monotone_path
  barrier_lt_iff

found at line 135 of 147, near the end of this file.

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


/-! Target module: LeanTest/HardProblems/Ruggedness.lean -/


/-!
# Directed paths and barrier heights

This module gives graph-level definitions of finite paths, local maxima, and
barriers. A positive barrier forces a dip below the starting value on every
path. An empty path family gives barrier `⊤`, distinguishing unreachability
from every finite barrier depth.
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

/-- Barrier height from `x` to `y`: the infimum, over admissible paths, of the
deepest dip below `J x` along the path (dips measured in `ℝ≥0∞`, so paths
that never dip contribute `0`). Empty infimum is `⊤`: no path, infinite
barrier. -/
noncomputable def barrier (Adj : X → X → Prop) (J : X → ℝ) (x y : X) : ℝ≥0∞ :=
  ⨅ γ : PathBetween Adj x y, ⨆ z ∈ γ.points, ENNReal.ofReal (J x - J z)

/-- A positive barrier means every admissible route to `y` contains a
configuration strictly worse than the start. No hypothesis here says that `y`
is better than the start or that the dip occurs before first reaching `y`. -/
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

/-- No admissible path at all makes the barrier infinite. -/
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

/-! ### Barriers as superlevel reachability

The barrier sits below a positive depth exactly when the target is reachable
through the corresponding strict superlevel region. -/

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

end HardProblems
