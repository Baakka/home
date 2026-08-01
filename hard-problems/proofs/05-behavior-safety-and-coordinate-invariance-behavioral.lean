import Mathlib

/-!
This snippet is about:

  Trajectory
  Behavior
  mapTrajectory
  hide
  interconnect
  hide_interconnect_subset
  hide_interconnect_strict_counterexample
  hide_equiv_symm
  IsSafe
  IsViable
  empty_behavior_safe
  empty_behavior_not_viable
  isSafe_mono
  isSafe_hide_iff
  isSafe_hide
  IsRun
  generatedBehavior
  generatedBehavior_safe_of_invariant
  generatedBehavior_safe_iff_invariant
  restrict
  Compatible
  existsUnique_glue
  admissible_glue_counterexample

found at line 322 of 323, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/Behavioral.lean -/


/-!
# Behavioral systems, hiding, gluing, and safety

This module formalizes a deliberately small fragment of behavioral systems
theory. A behavior is a set of trajectories on one declared signal boundary.
Interconnection is intersection only after that boundary has been aligned.
Hiding is direct image under a pointwise signal map. Local gluing concerns
ordinary functions on two overlapping time domains. Safety is universal over
the admitted behavior and may therefore hold vacuously when that behavior is
empty. The repo-only viability declarations at the end make that separation
explicit: the empty behavior is safe for every predicate but is not viable.

The declarations were first submitted as an Aristotle proof target pinned to
Lean and mathlib v4.28.0. The proofs below are checked on the repository's
v4.33.0-rc1 toolchain.
-/

namespace HardProblems
namespace Behavioral

universe u v w

/-- A complete signal trajectory on time domain `T`. -/
abbrev Trajectory (T : Type u) (W : Type v) := T → W

/-- A behavior is the set of trajectories admitted by a system model. -/
abbrev Behavior (T : Type u) (W : Type v) := Set (Trajectory T W)

/-- Apply a signal map pointwise to a trajectory. -/
def mapTrajectory {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (x : Trajectory T W) : Trajectory T V :=
  f ∘ x

/-- Hide or relabel signal coordinates by taking the direct image of a
behavior under the pointwise signal map. -/
def hide {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B : Behavior T W) : Behavior T V :=
  mapTrajectory f '' B

/-- On one already aligned signal boundary, behavioral interconnection imposes
both component constraints. -/
def interconnect {T : Type u} {W : Type v}
    (B₁ B₂ : Behavior T W) : Behavior T W :=
  B₁ ∩ B₂

/-- Hiding after interconnection is contained in interconnecting after hiding.
The reverse inclusion can fail because the two projected witnesses need not be
the same hidden trajectory. -/
theorem hide_interconnect_subset {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B₁ B₂ : Behavior T W) :
    hide f (interconnect B₁ B₂) ⊆
      interconnect (hide f B₁) (hide f B₂) := by
  rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
  exact ⟨⟨x, hx₁, rfl⟩, ⟨x, hx₂, rfl⟩⟩

/-- Explicit strictness witness: each component admits a different hidden Bool
trajectory with the same visible projection. The components are individually
viable, their interconnection is empty, but their visible projections have a
nonempty interconnection. -/
theorem hide_interconnect_strict_counterexample :
    let f : Bool × Bool → Bool := Prod.fst
    let x₀ : Trajectory Unit (Bool × Bool) := fun _ ↦ (false, false)
    let x₁ : Trajectory Unit (Bool × Bool) := fun _ ↦ (false, true)
    let B₀ : Behavior Unit (Bool × Bool) := {x₀}
    let B₁ : Behavior Unit (Bool × Bool) := {x₁}
    B₀.Nonempty ∧ B₁.Nonempty ∧ interconnect B₀ B₁ = ∅ ∧
      hide f (interconnect B₀ B₁) ⊂
        interconnect (hide f B₀) (hide f B₁) := by
  dsimp
  refine ⟨Set.singleton_nonempty _, Set.singleton_nonempty _, ?_⟩
  have hEmpty :
      interconnect ({fun _ : Unit ↦ (false, false)} :
        Behavior Unit (Bool × Bool)) {fun _ : Unit ↦ (false, true)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz₀, hz₁⟩
    rw [Set.mem_singleton_iff] at hz₀ hz₁
    have hEq : (fun _ : Unit ↦ (false, false)) =
        fun _ : Unit ↦ (false, true) := hz₀.symm.trans hz₁
    have := congrFun hEq ()
    simp at this
  refine ⟨hEmpty, ?_⟩
  refine Set.ssubset_iff_subset_ne.mpr
    ⟨hide_interconnect_subset _ _ _, ?_⟩
  intro hEq
  have hVisible : (fun _ : Unit ↦ false) ∈
      interconnect
        (hide Prod.fst ({fun _ : Unit ↦ (false, false)} :
          Behavior Unit (Bool × Bool)))
        (hide Prod.fst ({fun _ : Unit ↦ (false, true)} :
          Behavior Unit (Bool × Bool))) := by
    exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  have hImpossible : (fun _ : Unit ↦ false) ∈
      hide Prod.fst
        (interconnect ({fun _ : Unit ↦ (false, false)} :
          Behavior Unit (Bool × Bool)) {fun _ : Unit ↦ (false, true)}) := by
    rw [hEq]
    exact hVisible
  rw [hEmpty] at hImpossible
  rcases hImpossible with ⟨_, hmem, _⟩
  exact hmem

/-- Exact relabeling by an equivalence loses no behavior. -/
theorem hide_equiv_symm {T : Type u} {W : Type v} {V : Type w}
    (e : W ≃ V) (B : Behavior T W) :
    hide e.symm (hide e B) = B := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzx⟩
    have hzx' : z = x := by
      simpa [mapTrajectory, Function.comp_def] using hzx
    simpa [← hzx'] using hz
  · intro hx
    refine ⟨mapTrajectory e x, ⟨x, hx, rfl⟩, ?_⟩
    funext t
    simp [mapTrajectory, Function.comp_def]

/-- A temporal safety predicate holds at every time on every admitted
trajectory. -/
def IsSafe {T : Type u} {W : Type v}
    (B : Behavior T W) (Safe : W → Prop) : Prop :=
  ∀ x ∈ B, ∀ t, Safe (x t)

/-- Refining a behavior preserves every universal safety property. -/
theorem isSafe_mono {T : Type u} {W : Type v}
    {B B' : Behavior T W} {Safe : W → Prop}
    (hsub : B' ⊆ B) (h : IsSafe B Safe) : IsSafe B' Safe := by
  intro x hx t
  exact h x (hsub hx) t

/-- Direct-image hiding has an exact safety semantics: a visible predicate
holds on every projected trajectory exactly when its pullback holds on every
original trajectory. This says nothing about predicates on discarded signal
coordinates. -/
theorem isSafe_hide_iff {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B : Behavior T W) (SafeV : V → Prop) :
    IsSafe (hide f B) SafeV ↔ IsSafe B (SafeV ∘ f) := by
  constructor
  · intro h x hx t
    simpa [mapTrajectory, Function.comp_def] using
      h (mapTrajectory f x) ⟨x, hx, rfl⟩ t
  · rintro h _ ⟨x, hx, rfl⟩ t
    simpa [mapTrajectory, Function.comp_def] using h x hx t

/-- Hiding preserves a safety property only when the signal map carries the
declared internal safe set into the external one. -/
theorem isSafe_hide {T : Type u} {W : Type v} {V : Type w}
    {B : Behavior T W} {SafeW : W → Prop} {SafeV : V → Prop}
    (f : W → V) (hB : IsSafe B SafeW)
    (hmap : ∀ w, SafeW w → SafeV (f w)) :
    IsSafe (hide f B) SafeV := by
  rintro _ ⟨x, hx, rfl⟩ t
  exact hmap (x t) (hB x hx t)

/-- A discrete trajectory follows `step` at every successor time. -/
def IsRun {S : Type u} (step : S → S) (x : Trajectory ℕ S) : Prop :=
  ∀ n, x (n + 1) = step (x n)

/-- All runs whose initial state lies in `Init`. -/
def generatedBehavior {S : Type u} (step : S → S) (Init : Set S) :
    Behavior ℕ S :=
  {x | x 0 ∈ Init ∧ IsRun step x}

/-- Forward invariance gives all-time safety for every generated run. -/
theorem generatedBehavior_safe_of_invariant {S : Type u}
    {step : S → S} {Init Safe : Set S}
    (hInit : Init ⊆ Safe) (hInv : Set.MapsTo step Safe Safe) :
    IsSafe (generatedBehavior step Init) Safe := by
  rintro x ⟨hx₀, hrun⟩ n
  induction n with
  | zero => exact hInit hx₀
  | succ n ih =>
      rw [hrun n]
      exact hInv ih

/-- For the behavior generated from every state in `Safe`, temporal safety is
equivalent to one-step forward invariance. -/
theorem generatedBehavior_safe_iff_invariant {S : Type u}
    (step : S → S) (Safe : Set S) :
    IsSafe (generatedBehavior step Safe) Safe ↔
      Set.MapsTo step Safe Safe := by
  constructor
  · intro h s hs
    let x : Trajectory ℕ S := fun n ↦ Nat.rec s (fun _ current ↦ step current) n
    have hrun : IsRun step x := by
      intro n
      simp [x]
    have hx : x ∈ generatedBehavior step Safe := by
      exact ⟨by simpa [x] using hs, hrun⟩
    have hs₁ := h x hx 1
    change x 1 ∈ Safe at hs₁
    simpa [x] using hs₁
  · intro hInv
    exact generatedBehavior_safe_of_invariant (by exact fun _ h ↦ h) hInv

/-! ## Binary local gluing

This is the function-level gluing mechanism behind a sheaf semantics. It does
not assert that an arbitrary assignment of admissible local behaviors is a
sheaf; closure of admissibility under restriction and gluing is extra data.
-/

/-- Restrict a local trajectory from `I` to a smaller time domain `J`. -/
def restrict {T : Type u} {W : Type v} {I J : Set T}
    (hJI : J ⊆ I) (x : I → W) : J → W :=
  fun t ↦ x ⟨t.1, hJI t.2⟩

/-- Two local trajectories agree wherever their time domains overlap. -/
def Compatible {T : Type u} {W : Type v} {I J : Set T}
    (x : I → W) (y : J → W) : Prop :=
  ∀ (t : T) (htI : t ∈ I) (htJ : t ∈ J),
    x ⟨t, htI⟩ = y ⟨t, htJ⟩

/-- Compatible functions on two time domains have a unique global function on
their union with the prescribed restrictions. -/
theorem existsUnique_glue {T : Type u} {W : Type v} {I J : Set T}
    (x : I → W) (y : J → W) (hxy : Compatible x y) :
    ∃! z : ↥(I ∪ J) → W,
      restrict Set.subset_union_left z = x ∧
      restrict Set.subset_union_right z = y := by
  classical
  let z : ↥(I ∪ J) → W := fun t ↦
    if htI : (t : T) ∈ I then x ⟨t, htI⟩
    else y ⟨t, t.property.resolve_left htI⟩
  have hzI : restrict Set.subset_union_left z = x := by
    funext t
    simp [restrict, z]
  have hzJ : restrict Set.subset_union_right z = y := by
    funext t
    by_cases htI : (t : T) ∈ I
    · simpa [restrict, z, htI] using hxy t htI t.property
    · simp [restrict, z, htI]
  refine ⟨z, ⟨hzI, hzJ⟩, ?_⟩
  intro z' hz'
  funext t
  by_cases htI : (t : T) ∈ I
  · have h := congrFun hz'.1 (⟨t, htI⟩ : I)
    simpa [restrict, z, htI] using h
  · have htJ : (t : T) ∈ J := t.property.resolve_left htI
    have h := congrFun hz'.2 (⟨t, htJ⟩ : J)
    simpa [restrict, z, htI] using h

/-- Raw compatible functions glue, but a nonempty declared set of admissible
global trajectories need not contain that glue. Thus arbitrary local/global
admissibility data do not acquire the sheaf property for free. -/
theorem admissible_glue_counterexample :
    let I : Set Bool := {false}
    let J : Set Bool := {true}
    let x : I → Bool := fun _ ↦ false
    let y : J → Bool := fun _ ↦ true
    let G : Set (↥(I ∪ J) → Bool) := {fun _ ↦ false}
    Compatible x y ∧ G.Nonempty ∧
      ¬ ∃ z ∈ G,
        restrict Set.subset_union_left z = x ∧
        restrict Set.subset_union_right z = y := by
  dsimp
  refine ⟨?_, Set.singleton_nonempty _, ?_⟩
  · intro t htI htJ
    rw [Set.mem_singleton_iff] at htI htJ
    exact Bool.noConfusion (htI.symm.trans htJ)
  · rintro ⟨z, hz, ⟨_, hzJ⟩⟩
    subst z
    have h := congrFun hzJ (⟨true, by simp⟩ : (↑({true} : Set Bool)))
    simp [restrict] at h

/-! ## Viability boundary

These declarations are intentionally separate from universal safety. They were
added in the repository after the pinned Aristotle target was submitted.
-/

/-- A behavior is viable when it admits at least one trajectory. -/
def IsViable {T : Type u} {W : Type v} (B : Behavior T W) : Prop :=
  B.Nonempty

/-- Universal safety is vacuous on the empty behavior. -/
theorem empty_behavior_safe {T : Type u} {W : Type v} {Safe : W → Prop} :
    IsSafe (∅ : Behavior T W) Safe := by
  simp [IsSafe]

/-- The empty behavior is not viable. -/
theorem empty_behavior_not_viable {T : Type u} {W : Type v} :
    ¬ IsViable (∅ : Behavior T W) := by
  simp [IsViable]

end Behavioral
end HardProblems
