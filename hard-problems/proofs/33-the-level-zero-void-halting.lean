import Mathlib


/-!
# Hard Problems: the tower of representations (section 7.4, chapter 10)

Formal brackets around ontological revision, from below and from above.

From below, revision provably helps: `expansion_gain` (`Definability`) and
`exists_escape_hatch` (`Ruggedness`) show a single new predicate or a
re-description can turn an undecidable target decidable and an infinite
barrier into none.

From above, revision provably never finishes. `diagonal_escape` is the
diagonal core: no countably enumerated stock of decision rules is complete,
because the diagonal target flips each rule on its own index.
`no_final_stage` iterates it: every stage of any hierarchy of
countably-presented rule stocks misses a target of its own. And the level
zero void is not hypothetical: `halting_void` restates mathlib's
undecidability of the halting problem in this vocabulary.

What is deliberately *not* claimed here: the relativized version, that the
halting problem for machines with an oracle `A` is not decidable in `A`
(the Turing jump, `A <ᵀ A'`), is classical (Turing's ordinal logics, Post's
degrees of unsolvability) but is not yet in mathlib; mathlib has Turing
reducibility and degrees (`TuringReducible`, `TuringDegree`) without the
jump. The book therefore cites the jump rather than marking it
machine-checked.
-/

namespace HardProblems

/-- Cantor's diagonal at the level of decision rules: no countable
enumeration of rules is complete; the diagonal target flips each rule on
its own index and so escapes every entry. -/
theorem diagonal_escape (e : ℕ → ℕ → Bool) :
    ∃ f : ℕ → Bool, ∀ k, f ≠ e k :=
  ⟨fun n => !(e n n), fun k h => by simpa using congrFun h k⟩

/-- The tower does not close: every stage of an arbitrary hierarchy of
countably-presented rule stocks misses a target constructible from that
very stage. Enrichment is always worth something (`expansion_gain`) and
never finished. -/
theorem no_final_stage (stage : ℕ → ℕ → ℕ → Bool) (i : ℕ) :
    ∃ f : ℕ → Bool, ∀ k, f ≠ stage i k :=
  diagonal_escape (stage i)

/-- The level-zero void, concretely: whether a program halts on its own
description is not decidable by any program. Mathlib's halting problem in
this file's vocabulary. -/
theorem halting_void (n : ℕ) :
    ¬ComputablePred fun c : Nat.Partrec.Code => (c.eval n).Dom :=
  ComputablePred.halting_problem n

end HardProblems
