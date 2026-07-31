import Mathlib

/-!
This snippet is about:

  robustMenu
  obsEq_iff_eq_of_injective
  robustMenu_eq_of_injective
  no_ambiguity_of_injective

found at line 242 of 257, near the end of this file.

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

/-- A programmed macro over `G`: an effector whose effect is, from every
state, already reachable with `G`. This is exactly what software over
the same effectors can implement, including state-dependent dispatch. -/
def Programmed (G : Set (X → X)) (g : X → X) : Prop :=
  ∀ y : X, Reach G y (g y)

/-- Admitting a programmed macro as a new primitive changes nothing: the
reachable set is closed under everything software can add. -/
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

/-- A genuinely new effector can strictly enlarge reach: the wall
yields to hardware and to nothing else. -/
theorem exists_new_effector_enlarges_reach :
    ∃ (G : Set (Bool → Bool)) (g : Bool → Bool) (x z : Bool),
      Reach (insert g G) x z ∧ ¬ Reach G x z := by
  refine ⟨∅, Bool.not, false, true, ?_, ?_⟩
  · exact Reach.tail Reach.refl (Set.mem_insert _ _) rfl
  · intro h
    cases h with
    | tail hy hmem heq => exact hmem.elim

end ProgClosure


/-! ### Full observability retires the observer

Ported from the Aristotle target `FullObs`. -/

section FullObs
variable {S Ω A : Type*}

/-- Observational equivalence through a signal map: two states look
alike when they emit the same observation. -/
def ObsEq (obs : S → Ω) (s t : S) : Prop := obs s = obs t

/-- The robust menu at `s`: the actions acceptable in every state that
looks like `s`. -/
def robustMenu (obs : S → Ω) (Acc : S → Set A) (s : S) : Set A :=
  ⋂ t ∈ {t | ObsEq obs s t}, Acc t

/-- Under injective observation, looking alike is being equal. -/
theorem obsEq_iff_eq_of_injective {obs : S → Ω}
    (h : Function.Injective obs) (s t : S) :
    ObsEq obs s t ↔ s = t := by
  constructor
  · intro hObs
    exact h hObs
  · intro h
    rw [h]
    rfl

/-- Under injective observation, the robust menu is the acceptable set
itself: no acceptable action is lost to ambiguity. -/
theorem robustMenu_eq_of_injective {obs : S → Ω}
    (h : Function.Injective obs) (Acc : S → Set A) (s : S) :
    robustMenu obs Acc s = Acc s := by
  simp only [robustMenu]
  have : {t | ObsEq obs s t} = {s} := by
    ext t
    simp [obsEq_iff_eq_of_injective h]
  simp [this]

/-- Decision-critical ambiguity cannot occur under injective
observation: there are no look-alike states with a nonempty acceptable
set on one side and disjoint acceptable sets between them. -/
theorem no_ambiguity_of_injective {obs : S → Ω}
    (h : Function.Injective obs) (Acc : S → Set A) :
    ¬ ∃ s t : S, ObsEq obs s t ∧ (Acc s).Nonempty ∧
      Disjoint (Acc s) (Acc t) := by
  intro ⟨s, t, hObs, hNS, hDisj⟩
  have hs : s = t := h (by simpa [ObsEq] using hObs)
  rw [hs] at hDisj
  rw [Set.disjoint_iff_inter_eq_empty] at hDisj
  rw [Set.inter_self] at hDisj
  obtain ⟨x, hx⟩ := hNS
  rw [hs] at hx
  rw [hDisj] at hx
  exact hx

end FullObs
end HardProblems
