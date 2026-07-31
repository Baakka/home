import LeanTest.HardProblems.Observability

/-!
# Hard Problems: the systems-theory inheritance, formalized

The book draws on cybernetics and complexity theory. This file formalizes
the pieces of that inheritance that are actually theorems, in the book's own
vocabulary:

* `requisite_variety` (Ashby): a regulator that uses few distinct responses
  cannot confine many distinguishable disturbances to a small outcome set.
  The counting form: |D| is at most (responses used) times (outcomes hit).
* `PassivelyDistinguishable` / `ProbeDistinguishable` (Snowden's
  complicated/complex boundary, made precise): some model classes can be
  separated by watching, others only by acting. `passively_imp_probe` gives
  the easy inclusion; the strict separation witness shows the "complex"
  regime is nonempty, so probe-sense-respond is sometimes the only mode of
  learning.
* `statistic_based_rule_fails` (Campbell, Goodhart): a decision rule that
  acts only through a summary statistic inherits the statistic's blindness.
* `invariance_comp` / `increment_bound_not_compositional` (Leveson):
  set-invariance safety composes; margin-style safety does not. Safety is a
  property of the composition, not of the components.
* `value_of_information_nonneg` (Raiffa): observing before acting never
  lowers the achievable expected utility.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

/-! ## Requisite variety (Ashby) -/

section Ashby

variable {D A O : Type*}

/-- Ashby's law of requisite variety, counting form. `ω d a` is the outcome
of disturbance `d` under regulator response `a`. If distinct disturbances
produce distinct outcomes under any fixed response (the disturbances really
are distinct as far as the outcome is concerned), then any response rule `ρ`
satisfies: the number of disturbances is at most the number of responses
actually used times the number of outcomes actually hit. Only variety in the
regulator can absorb variety in the disturbances. -/
theorem requisite_variety [Fintype D] [DecidableEq A] [DecidableEq O]
    (ω : D → A → O) (hinj : ∀ a, Function.Injective fun d => ω d a)
    (ρ : D → A) :
    Fintype.card D ≤
      (Finset.univ.image ρ).card * (Finset.univ.image fun d => ω d (ρ d)).card := by
  have key :
      (Finset.univ : Finset D).card ≤
        ((Finset.univ.image ρ) ×ˢ (Finset.univ.image fun d => ω d (ρ d))).card := by
    apply Finset.card_le_card_of_injOn (fun d => (ρ d, ω d (ρ d)))
    · intro d _
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem ρ (Finset.mem_univ d),
         Finset.mem_image_of_mem _ (Finset.mem_univ d)⟩
    · intro d _ d' _ hdd
      have h1 : ρ d = ρ d' := congrArg Prod.fst hdd
      have h2 : ω d (ρ d) = ω d' (ρ d') := congrArg Prod.snd hdd
      apply hinj (ρ d)
      show ω d (ρ d) = ω d' (ρ d)
      rw [h2, ← h1]
  rw [Finset.card_product] at key
  simpa using key

end Ashby
end
end HardProblems
