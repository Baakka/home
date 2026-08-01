import Mathlib

/-!
This snippet is about:

  Envelope
  exists_bounded_optimum
  bounded_optimum_mono
  exists_strict_envelope_gap

found at line 62 of 71, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/ResourceBounds.lean -/


/-!
# Finite resource envelopes

These results formalize only a finite feasible-set reading of bounded
optimality. They establish existence and value monotonicity. They provide no
algorithm for finding an optimum and no complexity bound for doing so.

The proofs were produced by Harmonic's Aristotle prover against the statements
as written, verified against Lean/mathlib v4.28, and ported to this project's
toolchain.
-/

namespace HardProblems

/-- A resource envelope specifies which programs are admitted and requires the
admitted set to be finite. -/
structure Envelope (P : Type*) where
  admits : P → Prop
  finite : Set.Finite {p | admits p}

/-- A real-valued objective attains a maximum on any nonempty finite resource
envelope. This is an existence theorem, not an optimization procedure. -/
theorem exists_bounded_optimum {P : Type*} (E : Envelope P) (V : P → ℝ)
    (hne : ∃ p, E.admits p) :
    ∃ p, E.admits p ∧ ∀ q, E.admits q → V q ≤ V p := by
  obtain ⟨p, hp, hmax⟩ :=
    Set.exists_max_image {p | E.admits p} V E.finite hne
  exact ⟨p, hp, hmax⟩

/-- If one finite envelope is included in another, the value of an optimum in
the larger envelope is at least that of an optimum in the smaller envelope. -/
theorem bounded_optimum_mono {P : Type*} (E F : Envelope P) (V : P → ℝ)
    (hEF : ∀ p, E.admits p → F.admits p)
    (p : P) (hp : E.admits p) (_hopt : ∀ q, E.admits q → V q ≤ V p)
    (q : P) (_hq : F.admits q) (hqopt : ∀ r, F.admits r → V r ≤ V q) :
    V p ≤ V q := by
  exact hqopt p (hEF p hp)

/-- There is a nonempty finite envelope whose internal optimum is strictly
dominated by an excluded program. The witness's objective is unbounded, so the
statement deliberately does not claim that the excluded program is a global
optimum. -/
theorem exists_strict_envelope_gap :
    ∃ (E : Envelope ℕ) (V : ℕ → ℝ) (p : ℕ),
      E.admits p ∧ (∀ q, E.admits q → V q ≤ V p) ∧
      ∃ r, V p < V r := by
  use ⟨fun n => n = 0, by simp⟩
  use fun n => n
  use 0
  simp
  exact ⟨1, by norm_num⟩

end HardProblems
