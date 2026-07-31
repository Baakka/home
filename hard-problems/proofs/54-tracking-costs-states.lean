import Mathlib

/-!
This snippet is about:

  Tracks
  injective
  card_le_of_tracks
  card_eq_of_mutual_tracks

found at line 124 of 127, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/BoundedMachines.lean -/


/-!
# Agents as bounded machines

The framework's agents are resource-bounded machines, and this module is
the reading of the hardness profile that follows from taking that
literally. Its results are grouped by the claim they discharge:

* representation bounds (`card_le_of_tracks`, `card_eq_of_mutual_tracks`):
  faithfully tracking a machine costs at least its state count, so a
  smaller machine cannot represent a larger one and mutual modelling
  forces parity (book chapter 8);
* the action wall (`traj_mem_reach`, `reach_insert_programmed`,
  `exists_new_effector_enlarges_reach`): reachability is a property of
  the effector set, closed under everything a program can compose from
  it, and moved only by a new effector (chapter 4);
* the observation wall's converse (`robustMenu_eq_of_injective`,
  `no_ambiguity_of_injective`): when the observation map is injective the
  estimator machinery is vacuous (chapter 3);
* the scaling diagnostic (`mulLang_not_regular`): no finite-state machine
  verifies unary multiplication, so a constant-space agent degrades with
  problem size while nothing structural is wrong;
* online versus offline (`ascent_from_zero_stalls`, `route_to_max_exists`,
  `every_route_dips`): on one fixed landscape the neighbour-comparing
  searcher stalls where the map-holding searcher does not, and the
  barrier survives both (chapter 6);
* the ladder collapse (`Tuned.stateRun_eq_fst`, `card_fixed`) and the
  regress (`towerCard_strictMono`, `towerCard_unbounded`): self-tuning is
  one fixed machine on a product space, and augmenting against a modelled
  counterpart never closes (chapter 8).

Every proof in this file was produced by Harmonic's Aristotle prover
against the statements as written here, and re-checked locally.
-/

namespace HardProblems

/-! ### Representation bounds: tracking needs states

Ported from the Aristotle target `SimBound`. -/

section SimBound
/-- A deterministic machine with inputs `I`, outputs `O`, and state
space `S`: a step function and an output map. -/
structure Machine (I O S : Type*) where
  step : S → I → S
  out : S → O

variable {I O S T : Type*}

/-- Run a machine from state `s` on an input word `w`. -/
def Machine.run (M : Machine I O S) (s : S) (w : List I) : S :=
  w.foldl M.step s

/-- A machine is output-separated when any two states that agree on the
outputs along every input word are equal. -/
def Machine.Separated (M : Machine I O S) : Prop :=
  ∀ s t : S, (∀ w : List I, M.out (M.run s w) = M.out (M.run t w)) → s = t

/-- `f` tracks machine `B` inside machine `A`: the encoding intertwines
the dynamics and reproduces the outputs. This is what it means for `A`
to maintain a faithful copy of `B`. -/
structure Tracks (A : Machine I O S) (B : Machine I O T) (f : T → S) : Prop where
  step_eq : ∀ t i, f (B.step t i) = A.step (f t) i
  out_eq : ∀ t, A.out (f t) = B.out t

/-- A tracking map intertwines whole runs, not just single steps. -/
theorem Tracks.run_eq {A : Machine I O S} {B : Machine I O T} {f : T → S}
    (h : Tracks A B f) (t : T) (w : List I) :
    f (B.run t w) = A.run (f t) w := by
  induction w generalizing t with
  | nil => rfl
  | cons i w ih =>
    simp [Machine.run]
    rw [← h.step_eq]
    exact ih (B.step t i)

/-- Tracking an output-separated machine is injective: the tracker must
hold distinct internal states for distinct tracked states. -/
theorem Tracks.injective {A : Machine I O S} {B : Machine I O T} {f : T → S}
    (h : Tracks A B f) (hB : B.Separated) : Function.Injective f := by
  intro t₁ t₂ hft
  apply hB t₁ t₂
  intro w
  have eq1 : f (B.run t₁ w) = A.run (f t₁) w := h.run_eq t₁ w
  have eq2 : f (B.run t₂ w) = A.run (f t₂) w := h.run_eq t₂ w
  rw [← h.out_eq (B.run t₁ w), ← h.out_eq (B.run t₂ w), eq1, eq2, hft]

/-- The pigeonhole bound: a finite machine can faithfully track an
output-separated machine only if it has at least as many states.
"Something below you on the scale cannot represent you." -/
theorem card_le_of_tracks [Fintype S] [Fintype T]
    {A : Machine I O S} {B : Machine I O T} {f : T → S}
    (h : Tracks A B f) (hB : B.Separated) :
    Fintype.card T ≤ Fintype.card S := by
  exact Fintype.card_le_of_injective _ (Tracks.injective h hB)

/-- Mutual faithful tracking forces representational parity: if each of
two output-separated finite machines tracks the other, their state
counts are equal. Steering an equal is a different activity from
steering something smaller. -/
theorem card_eq_of_mutual_tracks [Fintype S] [Fintype T]
    {A : Machine I O S} {B : Machine I O T} {f : T → S} {g : S → T}
    (hf : Tracks A B f) (hg : Tracks B A g)
    (hA : A.Separated) (hB : B.Separated) :
    Fintype.card S = Fintype.card T := by
  exact le_antisymm (card_le_of_tracks hg hA) (card_le_of_tracks hf hB)

end SimBound
end HardProblems
