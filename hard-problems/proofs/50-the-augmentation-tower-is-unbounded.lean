import Mathlib

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


/-! ### Constant space fails multiplication at scale

Ported from the Aristotle target `RegMult`. -/

section RegMult
/-- The unary multiplication-verification language over a three-letter
alphabet: `m` copies of letter 0, then `n` copies of letter 1, then
`m * n` copies of letter 2. -/
def mulLang : Language (Fin 3) :=
  {w | ∃ m n : ℕ,
    w = List.replicate m (0 : Fin 3) ++ List.replicate n (1 : Fin 3) ++
        List.replicate (m * n) (2 : Fin 3)}

/-- A language is regular when some finite-state deterministic automaton
accepts exactly it. -/
def IsRegularLang (L : Language (Fin 3)) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (M : DFA (Fin 3) σ), M.accepts = L

/-- No finite-state machine verifies unary multiplication: registers
must grow with the task, which is the calculator's whole advantage and
the unaided person's whole deficit. -/
theorem mulLang_not_regular : ¬ IsRegularLang mulLang := by
  have encoding_unique : ∀ m n p m' n' p' : ℕ,
      List.replicate m (0 : Fin 3) ++ List.replicate n (1 : Fin 3) ++
          List.replicate p (2 : Fin 3) =
        List.replicate m' (0 : Fin 3) ++ List.replicate n' (1 : Fin 3) ++
          List.replicate p' (2 : Fin 3) →
      m = m' ∧ n = n' ∧ p = p' := by
    intro m n p m' n' p' h
    constructor
    · have hc := congrArg (List.count (0 : Fin 3)) h
      simpa [List.count_append, List.count_replicate] using hc
    constructor
    · have hc := congrArg (List.count (1 : Fin 3)) h
      simpa [List.count_append, List.count_replicate] using hc
    · have hc := congrArg (List.count (2 : Fin 3)) h
      simpa [List.count_append, List.count_replicate] using hc
  rintro ⟨σ, inst, M, hM⟩
  letI : Fintype σ := inst
  obtain ⟨k, l, hkl, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := ℕ)
    (fun n => M.eval (List.replicate n (0 : Fin 3)))
  let z := List.replicate 1 (1 : Fin 3) ++ List.replicate k (2 : Fin 3)
  have hk : List.replicate k (0 : Fin 3) ++ z ∈ M.accepts := by
    rw [hM]
    exact ⟨k, 1, by simp [z]⟩
  have hl : List.replicate l (0 : Fin 3) ++ z ∈ M.accepts := by
    rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append] at hk ⊢
    change M.evalFrom (M.eval (List.replicate l (0 : Fin 3))) z ∈ M.accept
    rw [← heq]
    exact hk
  rw [hM] at hl
  rcases hl with ⟨m, n, hmn⟩
  have hu := encoding_unique l 1 k m n (m * n) (by simpa [z, mulLang] using hmn)
  rcases hu with ⟨rfl, rfl, hu⟩
  simp at hu
  exact hkl hu

end RegMult


/-! ### Online and offline on the same ground

Ported from the Aristotle target `LocalSearch`. -/

section LocalSearch
/-- The path graph on five vertices: adjacent iff the indices differ by
one. -/
def pathAdj (i j : Fin 5) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- A two-peaked evaluation: a local peak at vertex 1, the global
maximum at vertex 4, and a dip at vertex 2 between them. -/
def J : Fin 5 → ℤ := ![0, 2, 1, 3, 5]

/-- A strict-ascent step: move to an adjacent, strictly better vertex.
Every greedy local searcher takes only such steps. -/
def Ascent (u v : Fin 5) : Prop := pathAdj u v ∧ J u < J v

/-- Vertex 1 is a strict local maximum and not the global maximum. -/
theorem one_is_lesser_peak :
    (∀ v, pathAdj 1 v → J v < J 1) ∧ J 1 < J 4 := by
  constructor
  · intro v hv
    fin_cases v <;> simp_all [pathAdj, J]
  · decide

/-- Every strict-ascent walk from vertex 0 stalls at vertex 1: the
reflexive-transitive closure of `Ascent` from 0 reaches only 0 and 1,
and no ascent step leaves 1. Being stuck is a fact about the local
rule. -/
theorem ascent_from_zero_stalls :
    (∀ v, Relation.ReflTransGen Ascent 0 v → v = 0 ∨ v = 1) ∧
    (∀ v, ¬ Ascent 1 v) := by
  have h1 : ∀ v, ¬ Ascent 1 v := by
    intro v hv
    simp [Ascent, pathAdj] at hv
    fin_cases v <;> simp [J] at hv
  constructor
  · intro v hv
    induction hv with
    | refl => left; rfl
    | tail ih a ih' =>
      rename_i b c
      rcases ih' with ih0 | ih1
      · simp [Ascent, pathAdj] at a
        fin_cases c <;> simp [ih0] at a ⊢
      · simp [ih1] at a
        exact absurd a (h1 c)
  · exact h1

/-- The same ground carries an admissible route from 0 to the global
maximum: unreachability was never the finding. -/
theorem route_to_max_exists : Relation.ReflTransGen pathAdj 0 4 := by
  have h01 : pathAdj (0 : Fin 5) (1 : Fin 5) := by simp [pathAdj]
  have h12 : pathAdj (1 : Fin 5) (2 : Fin 5) := by simp [pathAdj]
  have h23 : pathAdj (2 : Fin 5) (3 : Fin 5) := by simp [pathAdj]
  have h34 : pathAdj (3 : Fin 5) (4 : Fin 5) := by simp [pathAdj]
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.refl)
          h01)
        h12)
      h23)
    h34

private lemma adjacent_left_without_two (a b : Fin 5)
    (hab : pathAdj a b) (ha : a.val ≤ 1) (hb : b ≠ 2) : b.val ≤ 1 := by
  fin_cases a <;> fin_cases b <;> simp_all [pathAdj]

private lemma chain_from_left_visits_two (l : List (Fin 5))
    (hchain : l.Chain' pathAdj) (hhead : l.head? = some 0)
    (hlast : l.getLast? = some 4) : (2 : Fin 5) ∈ l := by
  by_contra hno
  have propagate : ∀ (xs : List (Fin 5)), xs.Chain' pathAdj →
      (∀ a ∈ xs.head?, a.val ≤ 1) → (2 : Fin 5) ∉ xs →
      ∀ x ∈ xs, x.val ≤ 1 := by
    intro xs hc
    induction xs with
    | nil => simp
    | cons a t ih =>
      intro ha hn x hx
      have ha' : a.val ≤ 1 := by simpa using ha
      rcases t with _ | ⟨b, t⟩
      · simp_all
      · cases hc with
        | cons_cons hab htail =>
          have hbne : b ≠ (2 : Fin 5) := by
            intro h
            apply hn
            simp [h]
          have hb : b.val ≤ 1 := adjacent_left_without_two a b hab ha' hbne
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ha'
          · exact ih htail (by simpa using hb) (by simp_all) x (by simpa using hx)
  have hall := propagate l hchain (by simp [hhead]) hno
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have := hall 4 (by simp)
  norm_num at this

/-- Every admissible route from 0 to 4 visits vertex 2, whose value
dips below the lesser peak: holding the map does not remove the
valley, it makes the valley a priced line item. -/
theorem every_route_dips (l : List (Fin 5)) (hchain : l.Chain' pathAdj)
    (hhead : l.head? = some 0) (hlast : l.getLast? = some 4) :
    (2 : Fin 5) ∈ l ∧ J 2 < J 1 := by
  constructor
  · exact chain_from_left_visits_two l hchain hhead hlast
  -- the target used `native_decide`, which adds a compiler-trusting axiom;
  -- this is a two-value comparison, so evaluate it in the kernel instead
  · simp [J]

end LocalSearch


/-! ### The tuning rungs collapse into one machine

Ported from the Aristotle target `Ladder`. -/

section Ladder
variable {S Θ I : Type*}

/-- A parameterized dynamics with a tuning rule: at each step the
current parameter drives the state update and is itself retuned from
experience. -/
structure Tuned (S Θ I : Type*) where
  step : Θ → S → I → S
  tune : Θ → S → I → Θ

/-- The state after running the tuned system on an input word. -/
def Tuned.stateRun (M : Tuned S Θ I) : S → Θ → List I → S
  | s, _, [] => s
  | s, θ, i :: w => M.stateRun (M.step θ s i) (M.tune θ s i) w

/-- The parameter after running the tuned system on an input word. -/
def Tuned.paramRun (M : Tuned S Θ I) : S → Θ → List I → Θ
  | _, θ, [] => θ
  | s, θ, i :: w => M.paramRun (M.step θ s i) (M.tune θ s i) w

/-- The tuner as one fixed step function on the product space: no
parameter is being "learned" anywhere the product machine can see; it
is ordinary state. -/
def Tuned.fixedStep (M : Tuned S Θ I) : S × Θ → I → S × Θ :=
  fun q i => (M.step q.2 q.1 i, M.tune q.2 q.1 i)

/-- The collapse, state coordinate: the tuned run is the first
projection of the fixed product machine's run. -/
theorem Tuned.stateRun_eq_fst (M : Tuned S Θ I) (s : S) (θ : Θ)
    (w : List I) :
    M.stateRun s θ w = (w.foldl M.fixedStep (s, θ)).1 := by
  induction w generalizing s θ with
  | nil => rfl
  | cons i w ih =>
    simp only [Tuned.stateRun, List.foldl]
    exact ih (M.step θ s i) (M.tune θ s i)

/-- The collapse, parameter coordinate: the tuning history is the
second projection of the same run. -/
theorem Tuned.paramRun_eq_snd (M : Tuned S Θ I) (s : S) (θ : Θ)
    (w : List I) :
    M.paramRun s θ w = (w.foldl M.fixedStep (s, θ)).2 := by
  induction w generalizing s θ with
  | nil => rfl
  | cons i w ih =>
    simp only [Tuned.paramRun, List.foldl]
    exact ih (M.step θ s i) (M.tune θ s i)

/-- The variety bill for the collapse: the fixed machine's state space
has product cardinality. -/
theorem card_fixed (S Θ : Type*) [Fintype S] [Fintype Θ] :
    Fintype.card (S × Θ) = Fintype.card S * Fintype.card Θ := by
  exact Fintype.card_prod S Θ

end Ladder


/-! ### The reflexive regress strictly grows state

Ported from the Aristotle target `Regress`. -/

section Regress
/-- The state count of the k-th augmentation round: start at `s`
states; each round pairs the current space with the counterpart's
policies over it (`p` actions). -/
def towerCard (s p : ℕ) : ℕ → ℕ
  | 0 => s
  | k + 1 => towerCard s p k * p ^ towerCard s p k

/-- With a nonempty base and at least two counterpart actions, every
augmentation round strictly grows the state count. -/
theorem towerCard_strictMono {s p : ℕ} (hs : 1 ≤ s) (hp : 2 ≤ p) :
    StrictMono (towerCard s p) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [towerCard]
  have hpos : 0 < towerCard s p k := by
    induction k with
    -- ported from the v4.28.0 target: `0 < s` no longer simp-normalizes to
    -- `1 ≤ s` on this toolchain, so convert explicitly
    | zero => simpa [towerCard] using Nat.lt_of_succ_le hs
    | succ k ih =>
      simp only [towerCard]
      positivity
  have hpow : 1 < p ^ towerCard s p k :=
    Nat.one_lt_pow (ne_of_gt hpos) hp
  nlinarith

/-- The tower is unbounded: no finite augmentation closes the regress. -/
theorem towerCard_unbounded {s p : ℕ} (hs : 1 ≤ s) (hp : 2 ≤ p) :
    ∀ N : ℕ, ∃ k : ℕ, N < towerCard s p k := by
  intro N
  have hmono := towerCard_strictMono hs hp
  exact
    ⟨N + 1,
      lt_of_le_of_lt (hmono.id_le N) (hmono (Nat.lt_succ_self N))⟩

end Regress
end HardProblems
