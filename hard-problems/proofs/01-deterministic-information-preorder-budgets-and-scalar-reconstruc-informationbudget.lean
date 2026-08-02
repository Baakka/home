import Mathlib

/-!
This snippet is about:

  accumulated_le_initial_add_rounds_mul
  required_excess_le_rounds_mul
  required_excess_div_capacity_le_rounds
  required_rounds_ceiling_le

found at line 106 of 110, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/InformationBudget.lean -/


/-!
# Scalar feedback budgets

This module isolates the arithmetic used by a feedback-capacity argument.  If
an accumulated scalar starts below `I₀` and increases by at most `C` in each
round, then after `n` rounds it is at most `I₀ + n * C`.  Consequently, a
threshold that has already been reached cannot exceed that budget.

The scalars can be instantiated with information quantities after the needed
information-theoretic inequalities have been proved elsewhere.  Nothing here
defines mutual information, proves a data-processing inequality, derives a
rate-distortion function, or shows that any physical feedback channel has
capacity `C`.  These are scalar budget lemmas, not Shannon theory.
-/

namespace HardProblems

namespace InformationBudget

/-- An accumulated real-valued quantity with initial upper bound `I₀` and
one-round increment bounded above by `C` is at most `I₀ + n * C` after `n`
rounds.

No nonnegativity hypothesis is needed for this arithmetic statement.  An
information-theoretic application must separately establish that its chosen
quantities and bounds have the intended meaning. -/
theorem accumulated_le_initial_add_rounds_mul
    (accumulated : ℕ → ℝ) (I₀ C : ℝ)
    (hinitial : accumulated 0 ≤ I₀)
    (hstep : ∀ n, accumulated (n + 1) ≤ accumulated n + C) :
    ∀ n, accumulated n ≤ I₀ + (n : ℝ) * C := by
  intro n
  induction n with
  | zero => simpa using hinitial
  | succ n ih =>
      calc
        accumulated (n + 1) ≤ accumulated n + C := hstep n
        _ ≤ (I₀ + (n : ℝ) * C) + C := add_le_add_left ih C
        _ = I₀ + ((n + 1 : ℕ) : ℝ) * C := by
          push_cast
          ring

/-- If reaching the target requires at least `R` units of the accumulated
quantity, and the target has been reached at round `n`, then the required
amount above the initial budget is no larger than `n * C`.

This conclusion is conditional on `hrequired`: the lemma does not prove that a
distortion level really requires `R`, nor that the accumulated scalar is
mutual information. -/
theorem required_excess_le_rounds_mul
    (accumulated : ℕ → ℝ) (I₀ C R : ℝ) (n : ℕ)
    (hinitial : accumulated 0 ≤ I₀)
    (hstep : ∀ k, accumulated (k + 1) ≤ accumulated k + C)
    (hrequired : R ≤ accumulated n) :
    R - I₀ ≤ (n : ℝ) * C := by
  have hbudget :=
    accumulated_le_initial_add_rounds_mul accumulated I₀ C hinitial hstep n
  linarith

/-- With positive per-round capacity, the real-valued required excess divided
by that capacity is a lower bound on the number of rounds.

This is only division of the preceding scalar inequality.  In particular, it
does not identify `R` with a rate-distortion function or `C` with Shannon
capacity. -/
theorem required_excess_div_capacity_le_rounds
    (accumulated : ℕ → ℝ) (I₀ C R : ℝ) (n : ℕ)
    (hinitial : accumulated 0 ≤ I₀)
    (hstep : ∀ k, accumulated (k + 1) ≤ accumulated k + C)
    (hrequired : R ≤ accumulated n) (hC : 0 < C) :
    (R - I₀) / C ≤ (n : ℝ) := by
  apply (div_le_iff₀ hC).2
  exact required_excess_le_rounds_mul accumulated I₀ C R n
    hinitial hstep hrequired

/-- Since rounds are natural numbers, the natural ceiling of the real-valued
ratio is also a lower bound on the round count.

If `R ≤ I₀`, the ratio may be nonpositive and the ceiling is zero; the theorem
then correctly gives only the vacuous lower bound `0 ≤ n`. -/
theorem required_rounds_ceiling_le
    (accumulated : ℕ → ℝ) (I₀ C R : ℝ) (n : ℕ)
    (hinitial : accumulated 0 ≤ I₀)
    (hstep : ∀ k, accumulated (k + 1) ≤ accumulated k + C)
    (hrequired : R ≤ accumulated n) (hC : 0 < C) :
    Nat.ceil ((R - I₀) / C) ≤ n := by
  apply Nat.ceil_le.mpr
  exact required_excess_div_capacity_le_rounds accumulated I₀ C R n
    hinitial hstep hrequired hC

end InformationBudget
end HardProblems
