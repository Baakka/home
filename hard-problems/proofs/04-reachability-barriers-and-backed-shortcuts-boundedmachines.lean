import Mathlib

/-!
This snippet is about:

  Reach
  traj_mem_reach
  Programmed
  reach_insert_programmed
  exists_new_effector_enlarges_reach

found at line 197 of 203, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/BoundedMachines.lean -/


/-!
# Bounded-machine examples

This module contains several independent finite-machine results: exact
tracking bounds, finite-composition reachability, injective observation, a
unary nonregularity example, one fixed local-search counterexample, product
state dynamics, and the growth of one explicitly defined augmentation
recurrence. Their interpretations remain tied to their individual hypotheses.
Most proofs were produced by Harmonic's Aristotle prover against the statements
as written and then checked locally.
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

/-- The pigeonhole bound: a finite machine can exactly track an
output-separated machine only if it has at least as many states. This is a
capacity bound for the stated exact tracking relation. -/
theorem card_le_of_tracks [Fintype S] [Fintype T]
    {A : Machine I O S} {B : Machine I O T} {f : T → S}
    (h : Tracks A B f) (hB : B.Separated) :
    Fintype.card T ≤ Fintype.card S := by
  exact Fintype.card_le_of_injective _ (Tracks.injective h hB)

/-- Mutual exact tracking forces cardinality parity for finite
output-separated machines. It does not by itself give an isomorphism between
their transition systems. -/
theorem card_eq_of_mutual_tracks [Fintype S] [Fintype T]
    {A : Machine I O S} {B : Machine I O T} {f : T → S} {g : S → T}
    (hf : Tracks A B f) (hg : Tracks B A g)
    (hA : A.Separated) (hB : B.Separated) :
    Fintype.card S = Fintype.card T := by
  exact le_antisymm (card_le_of_tracks hg hA) (card_le_of_tracks hf hB)

/-! Equal state counts are not sufficient for tracking. Ported from the
Aristotle target `CapacityCaveat`. -/

/-- A Boolean machine that flips at every input. -/
def flipMachine : Machine Unit Bool Bool where
  step s _ := !s
  out s := s

/-- A Boolean machine that never changes state. -/
def inertMachine : Machine Unit Bool Bool where
  step s _ := s
  out s := s

/-- Equal cardinality supplies no dynamical conjugacy. Output preservation
forces a proposed tracking map here to fix `false`, while transition
preservation would require the incompatible flip. -/
theorem same_cardinality_but_no_tracking :
    Fintype.card Bool = Fintype.card Bool ∧
      ¬ ∃ f : Bool → Bool, Tracks flipMachine inertMachine f := by
  constructor
  · rfl
  · rintro ⟨f, hf⟩
    have hfalse := hf.out_eq false
    have hstep := hf.step_eq false ()
    simp [flipMachine, inertMachine] at hfalse hstep

end SimBound


/-! ### The action wall: reach is a property of the effectors

Ported from the Aristotle target `ProgClosure`. -/

section ProgClosure
variable {X : Type*}

/-- Finite-composition reachability: `y` is reachable from `x` by
applying effectors drawn from `G`. -/
inductive Reach (G : Set (X → X)) (x : X) : X → Prop
  | refl : Reach G x x
  | tail : ∀ {y z : X} {g : X → X}, Reach G x y → g ∈ G → z = g y → Reach G x z

/-- Reachability is transitive. -/
theorem Reach.trans {G : Set (X → X)} {x y z : X}
    (hxy : Reach G x y) (hyz : Reach G y z) : Reach G x z := by
  induction hyz with
  | refl => exact hxy
  | tail hy hmem heq ih => exact Reach.tail ih hmem heq

/-- Any admissible trajectory stays inside the reachable set: at each
step some effector in `G` was applied, chosen by an arbitrary policy,
and no choice rule ever escapes the orbit. -/
theorem traj_mem_reach (G : Set (X → X)) (σ : ℕ → X)
    (hstep : ∀ n, ∃ g ∈ G, σ (n + 1) = g (σ n)) (n : ℕ) :
    Reach G (σ 0) (σ n) := by
  induction n with
  | zero => exact Reach.refl
  | succ n ih =>
      obtain ⟨g, hg, heq⟩ := hstep n
      exact Reach.tail ih hg heq

/-- Pointwise realizability over `G`: from every state, the image under `g` is
already reachable with `G`. The definition supplies neither a uniform generator
word nor a computable dispatcher for the witnessing paths. -/
def Programmed (G : Set (X → X)) (g : X → X) : Prop :=
  ∀ y : X, Reach G y (g y)

/-- Inserting a pointwise realizable transformation as a primitive leaves every
reachability orbit unchanged. -/
theorem reach_insert_programmed (G : Set (X → X)) {g : X → X}
    (hg : Programmed G g) (x z : X) :
    Reach (insert g G) x z ↔ Reach G x z := by
  constructor
  · intro h
    induction h with
    | refl => exact Reach.refl
    | @tail y z f hy hmem heq ih =>
        rcases hmem with (rfl | hmem)
        · rw [heq]
          exact Reach.trans ih (hg y)
        · exact Reach.tail ih hmem heq
  · intro h
    induction h with
    | refl => exact Reach.refl
    | tail hy hmem heq ih =>
        exact Reach.tail ih (Set.mem_insert_of_mem g hmem) heq

/-- A transformation outside the prior reachability closure can strictly
enlarge reach in an explicit two-state example. -/
theorem exists_new_effector_enlarges_reach :
    ∃ (G : Set (Bool → Bool)) (g : Bool → Bool) (x z : Bool),
      Reach (insert g G) x z ∧ ¬ Reach G x z := by
  refine ⟨∅, Bool.not, false, true, ?_, ?_⟩
  · exact Reach.tail Reach.refl (Set.mem_insert _ _) rfl
  · intro h
    cases h with
    | tail hy hmem heq => exact hmem.elim

end ProgClosure
end HardProblems
