import Mathlib

/-!
This snippet is about:

  ObsEquiv
  obsEquiv_equivalence
  DecisionCritical
  RobustAcceptable
  robustSet_eq_iInter
  RobustlyInfeasible
  robustlyInfeasible_iff_iInter_eq_empty
  no_robust_action

found at line 147 of 152, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Inlined dependency: LeanTest/HardProblems/Core.lean -/


/-!
# Core partially observed system

The companion modules share one small stochastic interface: a state transition
kernel controlled by an action and an observation kernel on the resulting state
space. More specialized task, policy, horizon, cost, and resource parameters
are introduced in the modules that use them.
-/

namespace HardProblems

/-- A countably supported partially observed stochastic system. The transition
kernel is action-indexed; the observation kernel emits a law from each latent
state. Admissible policy classes and resource bounds are separate parameters. -/
structure POSystem (S A O : Type*) where
  T : S → A → PMF S
  Z : S → PMF O

end HardProblems


/-! Target module: LeanTest/HardProblems/Observability.lean -/


/-!
# Observability and belief updates

Observational equivalence, decision-critical ambiguity, robust actions, and
the belief-state update.

Results proved here:

* `obsEquiv_equivalence`: observational equivalence (equality of the
  observation-process law under every probing policy and horizon) is an
  equivalence relation.
* `robustSet_eq_iInter`: a robust action is exactly a member of the
  intersection of acceptable sets over the equivalence class.
* `robustlyInfeasible_iff_iInter_eq_empty`: robust choice fails exactly when
  that total intersection is empty.
* `DecisionCritical.no_robust_action`: a disjoint equivalent pair is one
  sufficient certificate of robust infeasibility.
* `bayesUpdate`: the canonical belief update. Its well-definedness hypothesis
  `bayesEvidence ≠ 0` is not a technicality: it fails exactly when the
  observation has zero predictive probability under the maintained model.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

variable {S A O : Type*}

/-- The law of the focal observation sequence: run the maintained model `M`
for `n` steps from state `s` under a probing policy `π` (a function of the
observation history), returning the distribution over observation histories.
The accumulator `h` carries observations already made.

Timing convention: each round observes the current state, extends the history,
chooses an action, and then transitions. An `n`-round run therefore emits `n`
observations from `s_0, ..., s_(n-1)`; the terminal state `s_n` is not observed.
The Bayes definitions below are separate and use a predict-then-observe step. -/
def obsProcess (M : POSystem S A O) (π : List O → PMF A) :
    ℕ → S → List O → PMF (List O)
  | 0, _, h => PMF.pure h
  | n + 1, s, h =>
    (M.Z s).bind fun o =>
      (π (h ++ [o])).bind fun a =>
        (M.T s a).bind fun s' =>
          obsProcess M π n s' (h ++ [o])

/-- Observational equivalence: no policy of the declared function type
distinguishes the two states at any finite horizon. -/
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
the equivalence class of `s`. -/
theorem robustSet_eq_iInter (M : POSystem S A O) (Astar : S → Set A) (s : S) :
    {a | RobustAcceptable M Astar s a} = ⋂ s' ∈ {s' | ObsEquiv M s s'}, Astar s' := by
  ext a
  simp [RobustAcceptable]

/-- Robust choice is infeasible when no action is acceptable throughout the
observational equivalence class. -/
def RobustlyInfeasible (M : POSystem S A O) (Astar : S → Set A) (s : S) : Prop :=
  ¬ ∃ a, RobustAcceptable M Astar s a

/-- The exact criterion for robust infeasibility is emptiness of the total
intersection of acceptable-action sets over the observational class. Pairwise
disjointness is sufficient but not necessary for this intersection to be empty. -/
theorem robustlyInfeasible_iff_iInter_eq_empty
    (M : POSystem S A O) (Astar : S → Set A) (s : S) :
    RobustlyInfeasible M Astar s ↔
      ⋂ s' ∈ {s' | ObsEquiv M s s'}, Astar s' = ∅ := by
  rw [← robustSet_eq_iInter]
  change (¬ ({a | RobustAcceptable M Astar s a} : Set A).Nonempty) ↔ _
  exact Set.not_nonempty_iff_eq_empty

/-- A disjoint observationally equivalent pair certifies that no robust action
exists at the first state. -/
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
