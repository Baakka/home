import Mathlib


/-!
# Hard Problems: definability, signature adequacy, persistent ambiguity

Model-theoretic layer for chapters 3, 7.4, and 9. Two clusters:

**Vocabulary and resolution** (self-contained). A representation is modelled
as a set `L` of expressible predicates on the state space. `VocabEquiv L` is
the indistinguishability relation it induces, i.e. the resolution limit of
the representation. The main result, `exists_invariant_decider_iff`, is the
representational-adequacy criterion: a target set is decided by *some* rule
expressible in `L` iff it is a union of `L`-indistinguishability classes.
This generalizes `supportEquiv_iff_no_concept_separates` (`SystemsTheory`)
from concept lattices to arbitrary vocabularies, and `expansion_gain` is the
definability form of the ontological escape hatch (`exists_escape_hatch` in
`Ruggedness`): one new predicate that splits a class makes a previously
inexpressible target expressible. This separates the two grades of
misspecification in chapter 3: a false theory in an adequate signature is
repaired by updating; an inadequate signature is repaired only by expansion.

**Compactness and persistent ambiguity** (via `Mathlib.ModelTheory`). If two
rival hypotheses are each consistent with every *finite* batch of
observations, the compactness theorem produces full world histories
consistent with each (`rival_hypotheses_persist`). Decision-critical
ambiguity between axiomatizable hypotheses therefore cannot always be
resolved by more observation: the O coordinate of the hardness profile can
be pinned open by the logic itself, not merely by a shortage of data.
-/

namespace HardProblems

section Vocabulary

variable {X : Type*}

/-- Two states are `L`-indistinguishable when no predicate in the vocabulary
`L` separates them. `VocabEquiv L` is the finest distinction any rule phrased
in `L` can draw: the resolution limit of the representation. -/
def VocabEquiv (L : Set (X → Prop)) (x y : X) : Prop := ∀ P ∈ L, (P x ↔ P y)

/-- A decision rule is expressible in the vocabulary `L` if it never
separates `L`-indistinguishable states. -/
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

/-- **Representational adequacy.** A target set is decided by some rule
expressible in `L` iff it is a union of `L`-indistinguishability classes.
The left-to-right direction is the blind spot: below the resolution of the
vocabulary, no expressible rule can be correct. -/
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

end Vocabulary
end HardProblems
