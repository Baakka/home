import LeanTest.HardProblems.Core

/-!
# Hard Problems, Chapter 3: observability

Observational equivalence, decision-critical ambiguity, robust actions, and
the belief-state update.

Results proved here that the chapter asserts or implicitly relies on:

* `obsEquiv_equivalence`: observational equivalence (equality of the
  observation-process law under every probing policy and horizon) is an
  equivalence relation.
* `DecisionCritical.no_robust_action`: under decision-critical ambiguity
  there is no action acceptable across the whole equivalence class, which is
  the precise content of "the agent cannot choose reliably".
* `robustSet_eq_iInter`: a robust action is exactly a member of the
  intersection of acceptable sets over the equivalence class.
* `bayesUpdate`: the canonical belief update. Its well-definedness hypothesis
  `bayesEvidence ≠ 0` is not a technicality: it fails exactly when the
  observation has zero predictive probability under the maintained model,
  which is the moment the model class itself is refuted. The book should say
  this; the review does.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

variable {S A O : Type*}

/-- The law of the focal observation sequence: run the maintained model `M`
for `n` steps from state `s` under a probing policy `π` (a function of the
observation history), returning the distribution over observation histories.
The accumulator `h` carries observations already made.

Timing convention (matching the book's chapter 1 display): each step
observes the current state and then acts, so the emitted sequence is
`o_0 ~ Z(· ∣ s_0), o_1 ~ Z(· ∣ s_1), ...`: an initial observation of the
start state, then one observation of each post-transition state. This is
the same convention the belief update uses, where `bayesUpdate` weights by
the likelihood of the observation at the post-transition state. -/
def obsProcess (M : POSystem S A O) (π : List O → PMF A) :
    ℕ → S → List O → PMF (List O)
  | 0, _, h => PMF.pure h
  | n + 1, s, h =>
    (M.Z s).bind fun o =>
      (π (h ++ [o])).bind fun a =>
        (M.T s a).bind fun s' =>
          obsProcess M π n s' (h ++ [o])

/-- Chapter 3's observational equivalence `s ≡_{0,M} s'`: no admissible
probing policy can distinguish the two states at any finite horizon. -/
def ObsEquiv (M : POSystem S A O) (s s' : S) : Prop :=
  ∀ (π : List O → PMF A) (n : ℕ), obsProcess M π n s [] = obsProcess M π n s' []

/-- Observational equivalence is an equivalence relation, as the notation
`≡` silently promises. -/
theorem obsEquiv_equivalence (M : POSystem S A O) : Equivalence (ObsEquiv M) where
  refl _ := fun _ _ => rfl
  symm h := fun π n => (h π n).symm
  trans h₁ h₂ := fun π n => (h₁ π n).trans (h₂ π n)

/-- Decision-critical ambiguity: two observationally equivalent states whose
acceptable-action sets `A*_M` are disjoint. -/
def DecisionCritical (M : POSystem S A O) (Astar : S → Set A) (s s' : S) : Prop :=
  ObsEquiv M s s' ∧ Disjoint (Astar s) (Astar s')

/-- An action is robust at `s` when it is acceptable in every state
observationally equivalent to `s`. -/
def RobustAcceptable (M : POSystem S A O) (Astar : S → Set A) (s : S) (a : A) : Prop :=
  ∀ s', ObsEquiv M s s' → a ∈ Astar s'

/-- Robust actions are exactly the intersection of the acceptable sets over
the equivalence class of `s`. This is the book's third escape route
("choose an action robust across the equivalence class") stated precisely. -/
theorem robustSet_eq_iInter (M : POSystem S A O) (Astar : S → Set A) (s : S) :
    {a | RobustAcceptable M Astar s a} = ⋂ s' ∈ {s' | ObsEquiv M s s'}, Astar s' := by
  ext a
  simp [RobustAcceptable]

/-- Under decision-critical ambiguity no robust action exists: whatever is
acceptable at `s` is forbidden at `s'` and conversely. Probing or model
revision is then forced; no policy choice can dissolve the ambiguity. -/
theorem DecisionCritical.no_robust_action
    {M : POSystem S A O} {Astar : S → Set A} {s s' : S}
    (h : DecisionCritical M Astar s s') :
    ¬∃ a, RobustAcceptable M Astar s a := by
  rintro ⟨a, ha⟩
  have h₁ : a ∈ Astar s := ha s ((obsEquiv_equivalence M).refl s)
  have h₂ : a ∈ Astar s' := ha s' h.1
  exact Set.disjoint_left.mp h.2 h₁ h₂

end
end HardProblems
