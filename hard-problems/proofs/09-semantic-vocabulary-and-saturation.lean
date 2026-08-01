import Mathlib

/-!
This snippet is about:

  VocabEquiv
  VocabInvariant
  exists_invariant_decider_iff
  vocab_blind_spot
  expansion_gain

found at line 112 of 117, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/Definability.lean -/


/-!
# Predicate partitions and first-order compactness

Two clusters are formalized here:

**Vocabulary and resolution** (self-contained). A representation is modelled
as a set `L` of predicates on the state space. `VocabEquiv L` is the
equivalence relation induced by their truth values. The main result,
`exists_invariant_decider_iff`, is a semantic factorization criterion: a target
has a Boolean characteristic function constant on the induced classes iff it
is a union of those classes. It supplies neither a syntax nor a computable
decision procedure. `expansion_gain` inserts the target predicate itself and
is therefore a direct expressivity witness, not a discovery theorem.

**Compactness and persistent ambiguity** (via `Mathlib.ModelTheory`). If two
rival hypotheses are each consistent with every *finite* batch of
observations, the compactness theorem produces a model of the full observation
theory with each (`rival_hypotheses_persist`). It does not establish elementary
equivalence or equality under adaptive experiments.
-/

namespace HardProblems

section Vocabulary

variable {X : Type*}

/-- Two states are `L`-indistinguishable when every predicate in `L` has the
same truth value at both states. This is the equivalence relation induced by
the joint truth-value map for `L`; no syntax of `L`-formulas is assumed. -/
def VocabEquiv (L : Set (X → Prop)) (x y : X) : Prop := ∀ P ∈ L, (P x ↔ P y)

/-- A Boolean rule is invariant under the partition induced by `L` when it
never separates `L`-equivalent states. This is semantic fibre constancy, not
syntactic definability or computability. -/
def VocabInvariant (L : Set (X → Prop)) (d : X → Bool) : Prop :=
  ∀ ⦃x y⦄, VocabEquiv L x y → d x = d y

theorem VocabEquiv.refl (L : Set (X → Prop)) (x : X) : VocabEquiv L x x :=
  fun _ _ => Iff.rfl

theorem VocabEquiv.symm {L : Set (X → Prop)} {x y : X}
    (h : VocabEquiv L x y) : VocabEquiv L y x :=
  fun P hP => (h P hP).symm

theorem VocabEquiv.trans {L : Set (X → Prop)} {x y z : X}
    (hxy : VocabEquiv L x y) (hyz : VocabEquiv L y z) : VocabEquiv L x z :=
  fun P hP => (hxy P hP).trans (hyz P hP)

/-- A larger vocabulary draws finer distinctions: indistinguishability under
`L'` implies indistinguishability under any `L ⊆ L'`. -/
theorem VocabEquiv.mono {L L' : Set (X → Prop)} (hLL' : L ⊆ L') {x y : X}
    (h : VocabEquiv L' x y) : VocabEquiv L x y :=
  fun P hP => h P (hLL' hP)

/-- A target has a Boolean classifier constant on `L`-equivalence classes iff
the target is a union of those classes. The backward proof uses classical
decidability of membership and does not construct a computable classifier. -/
theorem exists_invariant_decider_iff (L : Set (X → Prop)) (F : Set X) :
    (∃ d : X → Bool, VocabInvariant L d ∧ ∀ x, d x = true ↔ x ∈ F) ↔
      ∀ x y, VocabEquiv L x y → (x ∈ F ↔ y ∈ F) := by
  classical
  constructor
  · rintro ⟨d, hd, hdF⟩ x y hxy
    rw [← hdF, ← hdF, hd hxy]
  · intro hF
    exact ⟨fun x => decide (x ∈ F),
      fun x y hxy => decide_eq_decide.mpr (hF x y hxy),
      fun x => by simp⟩

/-- If the target separates two `L`-indistinguishable states, every
`L`-invariant rule misclassifies at least one state. This is semantic fibre
constancy, not syntactic definability. -/
theorem vocab_blind_spot {L : Set (X → Prop)} {F : Set X} {x y : X}
    (hxy : VocabEquiv L x y) (hx : x ∈ F) (hy : y ∉ F) :
    ∀ d : X → Bool, VocabInvariant L d → ¬ ∀ z, (d z = true ↔ z ∈ F) := by
  intro d hd hdF
  exact hy ((hdF y).mp (by rw [← hd hxy]; exact (hdF x).mpr hx))

/-- Inserting the predicate `P` refines a class that `P` itself separates, so
the extension of `P` becomes fibre-classifiable in `insert P L`. Because the
new predicate is the target predicate, this is an upper-bound witness rather
than a construction or discovery result. -/
theorem expansion_gain {L : Set (X → Prop)} {P : X → Prop} {x y : X}
    (hxy : VocabEquiv L x y) (hPx : P x) (hPy : ¬ P y) :
    (¬ ∃ d : X → Bool, VocabInvariant L d ∧ ∀ z, d z = true ↔ z ∈ {z | P z}) ∧
      ∃ d : X → Bool, VocabInvariant (insert P L) d ∧
        ∀ z, d z = true ↔ z ∈ {z | P z} := by
  constructor
  · rw [exists_invariant_decider_iff]
    intro h
    exact hPy ((h x y hxy).mp hPx)
  · rw [exists_invariant_decider_iff]
    intro a b hab
    exact hab P (Set.mem_insert _ _)

end Vocabulary
end HardProblems
