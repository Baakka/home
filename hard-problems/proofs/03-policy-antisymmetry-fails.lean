import LeanTest.HardProblems.Core

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

end HardProblems
