import Mathlib

/-!
This snippet is about:

  run
  Indist
  run_conj
  indist_conj_iff
  reachableSet
  run_conj
  image_reachableSet_conj

found at line 125 of 128, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/Representation.lean -/


/-!
# Representation, coordinate change, and solution transfer

An invertible relabeling of the state space preserves the behavior carried
through that relabeling. This module records the deterministic reachability and
indistinguishability instances of that principle.

The results do not say that discovering or computing the equivalence is free.
They say only that once a conjugacy is supplied, a change of coordinates does
not alter the represented runs, observations, or reachable set.

The `SolutionTransfer` and `CoordinateBarrier` namespaces below incorporate
proofs produced by Harmonic's Aristotle prover against the submitted statements,
verified under Lean/mathlib v4.28, and then ported to this project's toolchain.
-/

namespace HardProblems

namespace Representation

/-- Drive deterministic dynamics with a finite input word, applying its
leftmost input first. -/
def run {U X : Type*} (step : U → X → X) : List U → X → X
  | [], x => x
  | u :: us, x => run step us (step u x)

end Representation

namespace CoordinateObservation

variable {U X X' Y : Type*}

open _root_.HardProblems.Representation

/-- Two states have identical outputs after every finite input word. -/
def Indist (step : U → X → X) (out : X → Y) (x x' : X) : Prop :=
  ∀ us : List U, out (run step us x) = out (run step us x')

/-- A conjugating equivalence commutes with every finite run. -/
theorem run_conj (e : X ≃ X') {step : U → X → X}
    {step' : U → X' → X'}
    (hstep : ∀ u x, e (step u x) = step' u (e x)) (us : List U) (x : X) :
    e (run step us x) = run step' us (e x) := by
  induction us generalizing x with
  | nil => rfl
  | cons u us ih =>
    simp only [run]
    rw [ih, hstep]

/-- Coordinate change preserves finite-word indistinguishability in both
directions when it conjugates transitions and preserves outputs. -/
theorem indist_conj_iff (e : X ≃ X') {step : U → X → X}
    {step' : U → X' → X'} {out : X → Y} {out' : X' → Y}
    (hstep : ∀ u x, e (step u x) = step' u (e x))
    (hout : ∀ x, out x = out' (e x)) (x y : X) :
    Indist step out x y ↔ Indist step' out' (e x) (e y) := by
  constructor
  · intro h us
    rw [← run_conj e hstep, ← run_conj e hstep]
    rw [← hout, ← hout]
    exact h us
  · intro h us
    rw [hout, hout]
    rw [run_conj e hstep, run_conj e hstep]
    exact h us

end CoordinateObservation

namespace CoordinateReach

variable {U X X' : Type*}

open _root_.HardProblems.Representation

/-- States reachable from `x` by some finite input word. -/
def reachableSet (step : U → X → X) (x : X) : Set X :=
  {z | ∃ us : List U, run step us x = z}

/-- A conjugating equivalence commutes with every finite run. -/
theorem run_conj (e : X ≃ X') {step : U → X → X}
    {step' : U → X' → X'}
    (hstep : ∀ u x, e (step u x) = step' u (e x)) (us : List U) (x : X) :
    e (run step us x) = run step' us (e x) := by
  induction us generalizing x with
  | nil => rfl
  | cons u us ih =>
    simp only [run]
    calc
      e (run step us (step u x)) = run step' us (e (step u x)) := ih _
      _ = run step' us (step' u (e x)) := congrArg (run step' us) (hstep u x)

/-- Coordinate change carries the concrete reachable set exactly onto the
reachable set in the conjugate coordinates. -/
theorem image_reachableSet_conj (e : X ≃ X') {step : U → X → X}
    {step' : U → X' → X'}
    (hstep : ∀ u x, e (step u x) = step' u (e x)) (x : X) :
    e '' reachableSet step x = reachableSet step' (e x) := by
  ext z
  constructor
  · rintro ⟨y, ⟨us, hus⟩, rfl⟩
    exact ⟨us, (run_conj e hstep us x).symm.trans (congrArg e hus)⟩
  · rintro ⟨us, hus⟩
    refine ⟨run step us x, ⟨us, rfl⟩, ?_⟩
    exact (run_conj e hstep us x).trans hus

end CoordinateReach
end HardProblems
