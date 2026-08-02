import Mathlib

/-!
This snippet is about:

  reachSet
  reachClosure
  reachSet_insert_programmed
  exists_strict_enlargement
  indistSaturation
  indistClosure
  indistClosure_le_of_refines
  behavioralClosure
  hide_interconnect_subset_and_strict
  ReindexCommutes
  addFalseClosure
  reindex_closure_need_not_commute
  reachSet_insert_const_true_strict
  reach_agrees
  indist_agrees
  hide_agrees
  programmed_agrees
  robustActions_agrees
  interconnect_agrees

found at line 2367 of 2375, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Inlined dependency: LeanTest/HardProblems/BoundedMachines.lean -/


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


/-! ### A unary multiplication language is not finite-state recognizable

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

/-- The unary multiplication-verification language is not regular. This is a
finite-state recognizability result, not a bound for positional multiplication
or a claim about any human or register architecture. -/
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

/-! The nonregularity result excludes finite-state recognizers. The definitions
below instead name an executable decider using natural-number counters and
multiplication, and prove its correctness. Merely asserting the existence of a
Boolean characteristic function would not supply a computable procedure. -/

/-- Strip a maximal run of the letter `a`, returning its length and the
remaining suffix. -/
def stripRun (a : Fin 3) : List (Fin 3) → ℕ × List (Fin 3)
  | [] => (0, [])
  | x :: xs =>
      if x = a then
        let r := stripRun a xs
        (r.1 + 1, r.2)
      else (0, x :: xs)

/-- An explicit decider: count the run of 0s, then of 1s, then of 2s, and
check that nothing is left over and that the last count is the product. -/
def mulDecide (w : List (Fin 3)) : Bool :=
  let r0 := stripRun 0 w
  let r1 := stripRun 1 r0.2
  let r2 := stripRun 2 r1.2
  r2.2.isEmpty && (r2.1 == r0.1 * r1.1)

lemma stripRun_reconstruct (a : Fin 3) (w : List (Fin 3)) :
    List.replicate (stripRun a w).1 a ++ (stripRun a w).2 = w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    simp only [stripRun]
    split
    · rename_i h
      simp only
      rw [List.replicate_succ]
      simp [ih, h]
    · rfl

lemma stripRun_replicate_append_of_not_mem (a : Fin 3) (n : ℕ)
    (xs : List (Fin 3)) (hxs : a ∉ xs) :
    stripRun a (List.replicate n a ++ xs) = (n, xs) := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    cases xs with
    | nil => rfl
    | cons x xs' =>
      simp_all [stripRun]
      intro h
      exact hxs.1 h.symm
  | succ n ih =>
    simp [List.replicate_succ, stripRun]
    exact ⟨congr_arg Prod.fst ih, congr_arg Prod.snd ih⟩

/-- The concrete procedure is correct. It uses natural-number counters and
multiplication, so this computability upper bound is not a finite-memory upper
bound. -/
theorem mulDecide_correct : ∀ w : List (Fin 3), mulDecide w = true ↔ w ∈ mulLang := by
  intro w
  constructor
  · intro h
    simp only [mulDecide, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
    rcases h with ⟨hrest, hcount⟩
    refine ⟨(stripRun 0 w).1, (stripRun 1 (stripRun 0 w).2).1, ?_⟩
    have h0 := stripRun_reconstruct 0 w
    have h1 := stripRun_reconstruct 1 (stripRun 0 w).2
    have h2 := stripRun_reconstruct 2 (stripRun 1 (stripRun 0 w).2).2
    calc
      w = List.replicate (stripRun 0 w).1 0 ++ (stripRun 0 w).2 := h0.symm
      _ = List.replicate (stripRun 0 w).1 0 ++
          (List.replicate (stripRun 1 (stripRun 0 w).2).1 1 ++
            (stripRun 1 (stripRun 0 w).2).2) := by rw [h1]
      _ = List.replicate (stripRun 0 w).1 0 ++
          (List.replicate (stripRun 1 (stripRun 0 w).2).1 1 ++
            (List.replicate (stripRun 2 (stripRun 1 (stripRun 0 w).2).2).1 2 ++
              (stripRun 2 (stripRun 1 (stripRun 0 w).2).2).2)) := by rw [h2]
      _ = List.replicate (stripRun 0 w).1 0 ++
          List.replicate (stripRun 1 (stripRun 0 w).2).1 1 ++
          List.replicate ((stripRun 0 w).1 * (stripRun 1 (stripRun 0 w).2).1) 2 := by
            rw [hrest, hcount]
            simp
  · rintro ⟨m, n, rfl⟩
    have h0 : (0 : Fin 3) ∉ List.replicate n 1 ++ List.replicate (m * n) 2 := by
      simp
    have hr0 := stripRun_replicate_append_of_not_mem 0 m
      (List.replicate n 1 ++ List.replicate (m * n) 2) h0
    have h1 : (1 : Fin 3) ∉ List.replicate (m * n) 2 := by
      simp
    have hr1 := stripRun_replicate_append_of_not_mem 1 n
      (List.replicate (m * n) 2) h1
    have hr2 := stripRun_replicate_append_of_not_mem 2 (m * n) [] (by simp)
    have hr2' : stripRun 2 (List.replicate (m * n) 2) = (m * n, []) := by
      simpa using hr2
    rw [List.append_assoc]
    simp only [mulDecide]
    rw [hr0, hr1, hr2']
    simp


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

/-- A strict-ascent local-search step: move to an adjacent, strictly better
vertex. -/
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
    (hchain : l.IsChain pathAdj) (hhead : l.head? = some 0)
    (hlast : l.getLast? = some 4) : (2 : Fin 5) ∈ l := by
  by_contra hno
  have propagate : ∀ (xs : List (Fin 5)), xs.IsChain pathAdj →
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

/-- Every admissible route from 0 to 4 visits vertex 2, whose value lies below
the lesser endpoint value. -/
theorem every_route_dips (l : List (Fin 5)) (hchain : l.IsChain pathAdj)
    (hhead : l.head? = some 0) (hlast : l.getLast? = some 4) :
    (2 : Fin 5) ∈ l ∧ J 2 < J 1 := by
  constructor
  · exact chain_from_left_visits_two l hchain hhead hlast
  -- Kernel reduction suffices for this two-value comparison.
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

/-- Represent the coupled state and parameter updates as one transition on the
product space. -/
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

/-- The product state space has the product of the two finite cardinalities. -/
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

/-- The explicitly defined full-policy augmentation recurrence is unbounded.
This does not rule out compact representations or fixed points for other
models. -/
theorem towerCard_unbounded {s p : ℕ} (hs : 1 ≤ s) (hp : 2 ≤ p) :
    ∀ N : ℕ, ∃ k : ℕ, N < towerCard s p k := by
  intro N
  have hmono := towerCard_strictMono hs hp
  exact
    ⟨N + 1,
      lt_of_le_of_lt (hmono.id_le N) (hmono (Nat.lt_succ_self N))⟩

/-- The type-level anchor: one augmentation round takes a finite state
space `A` to `A × (A → P)`, whose cardinality is the product-and-power
of the recursion above. -/
theorem card_augment (A P : Type*) [Fintype A] [Fintype P]
    [DecidableEq A] :
    Fintype.card (A × (A → P)) =
      Fintype.card A * Fintype.card P ^ Fintype.card A := by
  rw [Fintype.card_prod, Fintype.card_fun]

end Regress

end HardProblems


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


/-! Inlined dependency: LeanTest/HardProblems/Observability.lean -/


/-!
# Observability and belief updates

Observational equivalence, decision-critical ambiguity, robust actions, and
the belief-state update.

Results proved here:

* `obsEquiv_equivalence`: observational equivalence (equality of the
  observation-process law under every probing policy and horizon) is an
  equivalence relation.
* `common_estimate_forces_pairwise_convergence`: if one estimate converges to
  each of two trajectories, those trajectories converge to one another. This
  is the metric core of a necessary detectability condition.
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

open Filter
open scoped ENNReal Topology

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

/-- A necessary metric condition for asymptotic reconstruction: if the same
estimate converges to each of two state trajectories, their mutual distance
converges to zero. To turn this into a detectability theorem, a system-specific
argument must show that observationally indistinguishable trajectories really
feed the same estimate. -/
theorem common_estimate_forces_pairwise_convergence
    {X : Type*} [PseudoMetricSpace X] (x₁ x₂ xhat : ℕ → X)
    (h₁ : Tendsto (fun t => dist (x₁ t) (xhat t)) atTop (𝓝 0))
    (h₂ : Tendsto (fun t => dist (x₂ t) (xhat t)) atTop (𝓝 0)) :
    Tendsto (fun t => dist (x₁ t) (x₂ t)) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => dist_nonneg) (fun t => dist_triangle _ (xhat t) _) ?_
  have h₂' : Tendsto (fun t => dist (xhat t) (x₂ t)) atTop (𝓝 0) :=
    h₂.congr' (Eventually.of_forall fun t => dist_comm (x₂ t) (xhat t))
  simpa only [zero_add] using h₁.add h₂'

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

/-! ## The belief update

Given a prior belief `b`, an action-marginalized step kernel
`step = T_{θ,π₋₀}(· ∣ ·, a)`, and an observation kernel `Z`, the posterior
weight of `s'` is `Z s' o * (b.bind step) s'`, normalized by the total
predictive probability of the observation. -/

variable (b : PMF S) (step : S → PMF S) (Z : S → PMF O) (o : O)

/-- Predictive probability of observing `o` after one step from belief `b`:
the normalizer of Bayes' rule. -/
def bayesEvidence : ℝ≥0∞ :=
  ∑' s', Z s' o * (b.bind step) s'

/-- The evidence never exceeds one, hence is finite. -/
theorem bayesEvidence_le_one : bayesEvidence b step Z o ≤ 1 := by
  have h : ∀ s', Z s' o * (b.bind step) s' ≤ (b.bind step) s' := fun s' =>
    mul_le_of_le_one_left' (PMF.coe_le_one _ _)
  calc bayesEvidence b step Z o ≤ ∑' s', (b.bind step) s' := ENNReal.tsum_le_tsum h
    _ = 1 := (b.bind step).tsum_coe

/-- The canonical belief update. The hypothesis states that the observation has
positive probability under the current one-step predictive law. The definition
does not contain a model class or prescribe a response to zero evidence. -/
def bayesUpdate (h : bayesEvidence b step Z o ≠ 0) : PMF S :=
  PMF.normalize (fun s' => Z s' o * (b.bind step) s') h
    (lt_of_le_of_lt (bayesEvidence_le_one b step Z o) ENNReal.one_lt_top).ne

/-- The posterior is the likelihood-times-prediction, renormalized. -/
theorem bayesUpdate_apply (h : bayesEvidence b step Z o ≠ 0) (s' : S) :
    bayesUpdate b step Z o h s' =
      Z s' o * (b.bind step) s' * (bayesEvidence b step Z o)⁻¹ :=
  rfl

/-- The belief update extended by a declared default: when the observation has
zero predictive probability, keep the one-step prediction. The barycentre
theorem below does not depend on the choice on that zero-weight branch. -/
noncomputable def bayesUpdateOr : PMF S :=
  if h : bayesEvidence b step Z o ≠ 0 then bayesUpdate b step Z o h
  else b.bind step

/-- Barycentre consistency of Bayesian updating: the posterior, averaged over
the predictive observation law, is exactly the one-step prediction. This
identity does not say that individual posteriors are unchanged. -/
theorem tsum_bayesEvidence_mul_bayesUpdateOr (s' : S) :
    ∑' o, bayesEvidence b step Z o * bayesUpdateOr b step Z o s'
      = (b.bind step) s' := by
  have key : ∀ o : O, bayesEvidence b step Z o * bayesUpdateOr b step Z o s'
      = Z s' o * (b.bind step) s' := by
    intro o
    by_cases h : bayesEvidence b step Z o = 0
    · have hz : Z s' o * (b.bind step) s' = 0 := by
        have hle : Z s' o * (b.bind step) s' ≤ bayesEvidence b step Z o :=
          ENNReal.le_tsum s'
        simpa [h, nonpos_iff_eq_zero] using hle
      rw [h, zero_mul, hz]
    · have hfin : bayesEvidence b step Z o ≠ ⊤ :=
        (lt_of_le_of_lt (bayesEvidence_le_one b step Z o) ENNReal.one_lt_top).ne
      unfold bayesUpdateOr
      rw [dif_pos h, bayesUpdate_apply, mul_left_comm,
        ENNReal.mul_inv_cancel h hfin, mul_one]
  rw [tsum_congr key, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ## The belief-MDP bridge

The belief process is itself a Markov process on `PMF S`: sample the next
observation from its predictive law, update. `evidencePMF` packages the
Bayes normalizers as that predictive law (total mass one is Fubini), and
`beliefKernel` is the resulting one-step kernel on belief space. -/

/-- The predictive law of the next observation under belief `b`: the Bayes
normalizers, packaged as a distribution over observations. -/
def evidencePMF (b : PMF S) (step : S → PMF S) (Z : S → PMF O) : PMF O :=
  ⟨fun o => bayesEvidence b step Z o, by
    have h : ∑' o, bayesEvidence b step Z o = 1 := by
      unfold bayesEvidence
      rw [ENNReal.tsum_comm]
      calc ∑' s', ∑' o, Z s' o * (b.bind step) s'
          = ∑' s', (∑' o, Z s' o) * (b.bind step) s' :=
            tsum_congr fun s' => ENNReal.tsum_mul_right
        _ = ∑' s', (b.bind step) s' := by simp
        _ = 1 := (b.bind step).tsum_coe
    rw [← h]
    exact ENNReal.summable.hasSum⟩

@[simp] theorem evidencePMF_apply (o : O) :
    evidencePMF b step Z o = bayesEvidence b step Z o :=
  rfl

/-- One Markov step of the belief process: draw the observation from its
predictive law, then update. Beliefs thereby evolve as an ordinary Markov
process on the space `PMF S` under the supplied update rule. -/
def beliefKernel (step : S → PMF S) (Z : S → PMF O) (b : PMF S) : PMF (PMF S) :=
  (evidencePMF b step Z).bind fun o => PMF.pure (bayesUpdateOr b step Z o)

/-- Barycenter consistency of the belief kernel: averaging the next belief
over the observation law is the one-step prediction. Observations move
beliefs around; their mean moves by the dynamics alone. -/
theorem beliefKernel_bind_id (b : PMF S) (step : S → PMF S) (Z : S → PMF O) :
    (beliefKernel step Z b).bind id = b.bind step := by
  ext s'
  rw [beliefKernel, PMF.bind_bind]
  simp only [PMF.pure_bind, id_eq]
  rw [PMF.bind_apply]
  exact tsum_bayesEvidence_mul_bayesUpdateOr b step Z s'

/-! ## Zero evidence and full-support contamination

A zero normalizer means that every state with positive predictive mass assigns
zero likelihood to the observation. Adding a positive-weight full-support
contamination component makes every observation have positive predictive
probability. These are properties of the declared probability laws; they do
not formalize a class of models or a revision procedure. -/

/-- The localization: evidence dies exactly when every state the prediction
reaches makes the observation impossible. -/
theorem bayesEvidence_eq_zero_iff :
    bayesEvidence b step Z o = 0 ↔
      ∀ s', Z s' o = 0 ∨ (b.bind step) s' = 0 := by
  rw [bayesEvidence, ENNReal.tsum_eq_zero]
  exact forall_congr' fun s' => mul_eq_zero

/-- ε-contamination of an observation model: with weight `1 - ε` observe
through `Z`, with weight `ε` through the contamination `ζ`. -/
def contaminate (ε : ℝ≥0∞) (hε : ε ≤ 1) (Zobs ζ : S → PMF O) :
    S → PMF O := fun s =>
  ⟨fun o' => (1 - ε) * Zobs s o' + ε * ζ s o', by
    have h : ∑' o', ((1 - ε) * Zobs s o' + ε * ζ s o') = 1 := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        (Zobs s).tsum_coe, (ζ s).tsum_coe, mul_one, mul_one,
        tsub_add_cancel_of_le hε]
    have hs : HasSum (fun o' => (1 - ε) * Zobs s o' + ε * ζ s o')
        (∑' o', ((1 - ε) * Zobs s o' + ε * ζ s o')) := ENNReal.summable.hasSum
    rw [h] at hs
    exact hs⟩

/-- If the contamination component has full support and positive mixture
weight, every observation has positive evidence under the contaminated
kernel, for every prior and step kernel. -/
theorem bayesEvidence_mixture_pos (Zobs ζ : S → PMF O) {ε : ℝ≥0∞}
    (hε : ε ≤ 1) (hε0 : ε ≠ 0) (hζ : ∀ s o', ζ s o' ≠ 0) :
    bayesEvidence b step (contaminate ε hε Zobs ζ) o ≠ 0 := by
  intro h
  rw [bayesEvidence_eq_zero_iff] at h
  have hpred : ∀ s', (b.bind step) s' = 0 := by
    intro s'
    rcases h s' with h1 | h2
    · exfalso
      have hval : (contaminate ε hε Zobs ζ) s' o
          = (1 - ε) * Zobs s' o + ε * ζ s' o := rfl
      rw [hval, add_eq_zero] at h1
      rcases mul_eq_zero.mp h1.2 with hA | hB
      · exact hε0 hA
      · exact hζ s' o hB
    · exact h2
  have hone : (1 : ℝ≥0∞) = 0 := by
    rw [← (b.bind step).tsum_coe, tsum_congr hpred, tsum_zero]
  exact one_ne_zero hone

end

end HardProblems


/-! Inlined dependency: LeanTest/HardProblems/SystemsTheory.lean -/


/-!
# Counting, probing, statistics, and value of information

This file collects independent formal results used by the manuscript:

* `requisite_variety`: a response rule that uses few distinct responses
  cannot confine many distinguishable disturbances to a small outcome set.
  The counting form: |D| is at most (responses used) times (outcomes hit).
* `PassivelyDistinguishable` / `ProbeDistinguishable`: some model pairs agree
  under a selected constant action but differ under another policy.
* `statistic_based_rule_fails`: a decision rule that
  acts only through a summary statistic inherits the statistic's blindness.
* `invariance_comp` / `increment_bound_not_compositional`: set invariance is
  closed under composition, while the same unit increment bound is not.
* `value_of_information_nonneg`: optimizing after observing an outcome never
  lowers the nonnegatively weighted utility optimum.
-/

namespace HardProblems

noncomputable section

open scoped ENNReal

/-! ## Finite response and outcome counting -/

section Counting

variable {D A O : Type*}

/-- The separation a counting bound actually needs: two disturbances that the
regulator answers the same way must be told apart by that shared response.
Nothing is required of responses the rule never issues, or of pairs it answers
differently, because the bound already charges for the difference in response.

Demanding that *every* response separate *every* pair, which is how the law is
usually stated informally, is sufficient but strictly stronger:
`fiberSeparating_of_injective` gives the implication and
`fiberSeparating_strictly_weaker` witnesses that it does not reverse. -/
def FiberSeparating (ω : D → A → O) (ρ : D → A) : Prop :=
  ∀ d d', ρ d = ρ d' → ω d (ρ d) = ω d' (ρ d') → d = d'

/-- The informal premise implies the one the counting argument uses. -/
theorem fiberSeparating_of_injective (ω : D → A → O)
    (hinj : ∀ a, Function.Injective fun d => ω d a) (ρ : D → A) :
    FiberSeparating ω ρ := by
  intro d d' h1 h2
  apply hinj (ρ d)
  show ω d (ρ d) = ω d' (ρ d)
  rw [h2, ← h1]

/-- Finite counting form. `ω d a` is the outcome
of disturbance `d` under regulator response `a`. If the response rule `ρ`
separates the disturbances it answers alike (`FiberSeparating`), then the
number of disturbances is at most the number of responses actually used times
the number of outcomes actually hit. -/
theorem requisite_variety [Fintype D] [DecidableEq A] [DecidableEq O]
    (ω : D → A → O) (ρ : D → A) (hsep : FiberSeparating ω ρ) :
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
      exact hsep d d' (congrArg Prod.fst hdd) (congrArg Prod.snd hdd)
  rw [Finset.card_product] at key
  simpa using key

/-- The separation premise is load-bearing, not decoration. Drop it and the
inequality is false: two disturbances, one response, one outcome gives
`2 ≤ 1 * 1`. -/
theorem requisite_variety_fails_without_separation :
    ¬ ∀ (ω : Bool → Unit → Unit) (ρ : Bool → Unit),
        Fintype.card Bool ≤
          (Finset.univ.image ρ).card *
            (Finset.univ.image fun d => ω d (ρ d)).card := by
  intro h
  have := h (fun _ _ => ()) (fun _ => ())
  simp at this

/-- Fiberwise separation is strictly weaker than separation under every fixed
response. The rule `ρ = id` answers each disturbance its own way, so every
fiber is a singleton and separation is free, while the response `false`
collapses both disturbances to the same outcome. A bound that assumed the
informal premise would exclude this regulator for no reason. -/
theorem fiberSeparating_strictly_weaker :
    ∃ (ω : Bool → Bool → Bool) (ρ : Bool → Bool),
      FiberSeparating ω ρ ∧ ¬ ∀ a, Function.Injective fun d => ω d a := by
  refine ⟨fun d a => if a then d else false, id, ?_, ?_⟩
  · intro d d' h1 _
    exact h1
  · intro hinj
    have := hinj false (a₁ := true) (a₂ := false) rfl
    simp at this

/-- Perfect regulation: holding the outcome constant requires at least as
much response variety as there is disturbance variety. -/
theorem requisite_variety_perfect [Fintype D] [DecidableEq A] [DecidableEq O]
    (ω : D → A → O) (ρ : D → A) (hsep : FiberSeparating ω ρ)
    (o₀ : O) (hperf : ∀ d, ω d (ρ d) = o₀) :
    Fintype.card D ≤ (Finset.univ.image ρ).card := by
  have h := requisite_variety ω ρ hsep
  have himg : (Finset.univ.image fun d => ω d (ρ d)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d', _, rfl⟩ := Finset.mem_image.mp hy
    rw [hperf d, hperf d']
  calc Fintype.card D
      ≤ (Finset.univ.image ρ).card * (Finset.univ.image fun d => ω d (ρ d)).card := h
    _ ≤ (Finset.univ.image ρ).card * 1 :=
        Nat.mul_le_mul_left _ himg
    _ = (Finset.univ.image ρ).card := Nat.mul_one _

end Counting

/-! ## Constant-action and policy-dependent distinguishability -/

section Probes

variable {S A O : Type*}

/-- Two models are distinguishable from `s` under the constant action `a₀`
when their observation-history laws differ at some horizon. The type does not
assert that `a₀` is inert; that interpretation is supplied by an application. -/
def PassivelyDistinguishable (M₁ M₂ : POSystem S A O) (a₀ : A) (s : S) : Prop :=
  ∃ n, obsProcess M₁ (fun _ => PMF.pure a₀) n s [] ≠
        obsProcess M₂ (fun _ => PMF.pure a₀) n s []

/-- Two models are probe distinguishable from `s` when some policy of the
declared function type separates their observation-history laws. -/
def ProbeDistinguishable (M₁ M₂ : POSystem S A O) (s : S) : Prop :=
  ∃ (π : List O → PMF A) (n : ℕ),
    obsProcess M₁ π n s [] ≠ obsProcess M₂ π n s []

/-- A constant-action policy is a special case of an observation-dependent
policy. -/
theorem passively_imp_probe {M₁ M₂ : POSystem S A O} {a₀ : A} {s : S}
    (h : PassivelyDistinguishable M₁ M₂ a₀ s) : ProbeDistinguishable M₁ M₂ s :=
  let ⟨n, hn⟩ := h
  ⟨fun _ => PMF.pure a₀, n, hn⟩

/-- If two models agree on the observation kernel and on the transition kernel
at `a₀`, their laws under the constant-`a₀` policy agree at every horizon. -/
theorem obsProcess_congr_null (M₁ M₂ : POSystem S A O) (a₀ : A)
    (hZ : M₁.Z = M₂.Z) (hT : ∀ s, M₁.T s a₀ = M₂.T s a₀) :
    ∀ (n : ℕ) (s : S) (h : List O),
      obsProcess M₁ (fun _ => PMF.pure a₀) n s h =
        obsProcess M₂ (fun _ => PMF.pure a₀) n s h := by
  intro n
  induction n with
  | zero => intro s h; rfl
  | succ n ih =>
    intro s h
    simp only [obsProcess, PMF.pure_bind, hZ, hT, ih]

/-- Witness model: the state is observed exactly, the passive action `false`
leaves the state alone, and the probe action `true` flips it. -/
noncomputable def flipModel : POSystem Bool Bool Bool where
  T := fun s a => PMF.pure (if a then !s else s)
  Z := fun s => PMF.pure s

/-- Witness model: the state is observed exactly and never changes, whatever
the action. -/
noncomputable def inertModel : POSystem Bool Bool Bool where
  T := fun s _ => PMF.pure s
  Z := fun s => PMF.pure s

/-- There are two Boolean models whose laws agree under the constant action
`false` at every horizon but differ under the constant action `true`. In these
witness models, `false` is inert and `true` changes one model only. -/
theorem exists_probe_only_distinguishable :
    ∃ (M₁ M₂ : POSystem Bool Bool Bool) (s : Bool),
      ¬ PassivelyDistinguishable M₁ M₂ false s ∧ ProbeDistinguishable M₁ M₂ s := by
  refine ⟨flipModel, inertModel, false, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    exact hn (obsProcess_congr_null flipModel inertModel false rfl
      (fun s => by simp [flipModel, inertModel]) n false [])
  · refine ⟨fun _ => PMF.pure true, 2, ?_⟩
    have h₁ : obsProcess flipModel (fun _ => PMF.pure true) 2 false [] =
        PMF.pure [false, true] := by
      simp [obsProcess, flipModel, PMF.pure_bind]
    have h₂ : obsProcess inertModel (fun _ => PMF.pure true) 2 false [] =
        PMF.pure [false, false] := by
      simp [obsProcess, inertModel, PMF.pure_bind]
    rw [h₁, h₂]
    intro hcontra
    have := congrArg (fun p => p [false, true]) hcontra
    simp [PMF.pure_apply] at this

end Probes

/-! ## Statistic-factorized rules -/

section Statistics

variable {S A : Type*}

/-- A decision rule that acts only through a summary statistic inherits the
statistic's blindness: if the statistic identifies two states whose
acceptable-action sets are disjoint, then every rule based on it acts
unacceptably in at least one of the two. This is a sufficient pairwise
obstruction, not an exact characterization of safe statistic-based choice. -/
theorem statistic_based_rule_fails {m : S → ℝ} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : ℝ → A) :
    α (m s) ∉ Astar s ∨ α (m s') ∉ Astar s' := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  rw [hm] at h1
  exact Set.disjoint_left.mp hdisj h1 h2

/-- The statistic-factorization obstruction with an arbitrary statistic
codomain; nothing in the argument uses the real numbers. -/
theorem statistic_based_rule_fails' {Y : Type*} {m : S → Y} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : Y → A) :
    α (m s) ∉ Astar s ∨ α (m s') ∉ Astar s' := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  rw [hm] at h1
  exact Set.disjoint_left.mp hdisj h1 h2

/-- The randomized version: a stochastic rule that acts only through the
statistic cannot be supported inside both acceptable sets either. Whatever
it randomizes over, some realization it actually plays is unacceptable in
one of the two conflated states. -/
theorem statistic_based_randomized_rule_fails {m : S → ℝ} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : ℝ → PMF A) :
    ¬((α (m s)).support ⊆ Astar s ∧ (α (m s')).support ⊆ Astar s') := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := (α (m s)).support_nonempty
  have ha' : a ∈ (α (m s')).support := by rw [← hm]; exact ha
  exact Set.disjoint_left.mp hdisj (h1 ha) (h2 ha')

/-! `statistic_based_randomized_rule_fails` reads "acts unacceptably" as
playing an unacceptable action somewhere in the support, which is the right
reading for a `PMF` and gets normalization for free, since a `PMF` sums to one
by construction. It is the wrong reading for a distribution with no atoms at
all: a continuous law can be supported entirely outside the acceptable set
while every single action has probability zero, and a support-based statement
says nothing useful there.

So the same obstruction is stated once more for an arbitrary probability
measure, where acting unacceptably means failing to be *almost surely*
acceptable. The acceptable sets need not even be measurable, because the
conclusion is phrased through almost-everywhere membership rather than through
the measure of a complement.

This generalization is Aristotle's, from an independent formalization of the
same informal claim; the support-based version above is this project's. Its own
discrete formulation rolled a distribution structure by hand and then needed
normalization as an explicit side condition, with a counterexample showing why.
Using mathlib's `PMF` and `ProbabilityMeasure` sidesteps that entirely, so only
the generalization is kept here. -/

/-- `f` factors through `q` when all information used by `f` passes through
`q`. -/
def FactorsThrough {X Q Y : Type*} (f : X → Y) (q : X → Q) : Prop :=
  ∃ g : Q → Y, f = g ∘ q

/-- A function factoring through a map is constant on each fibre of that map. -/
theorem FactorsThrough.eq_of_eq {X Q Y : Type*} {f : X → Y} {q : X → Q}
    (hf : FactorsThrough f q) {x y : X} (hxy : q x = q y) : f x = f y := by
  obtain ⟨g, hg⟩ := hf
  simp [hg, hxy]

/-- A measure-theoretic randomized decision is acceptable at `s` when it is
supported on acceptable actions up to a null set. -/
def AlmostSurelyAcceptableAt {State Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action)
    (decision : State → MeasureTheory.ProbabilityMeasure Action) (s : State) : Prop :=
  ∀ᵐ a ∂(decision s : MeasureTheory.Measure Action), a ∈ acceptable s

/-- For an arbitrary probability measure, “acts unacceptably” means failure to
be almost surely supported on the acceptable set.  When the set is measurable,
this is equivalent to assigning positive mass to its complement. -/
def MeasureRandomizedUnacceptableAt {State Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action)
    (decision : State → MeasureTheory.ProbabilityMeasure Action) (s : State) : Prop :=
  ¬ AlmostSurelyAcceptableAt acceptable decision s

private lemma probabilityMeasure_not_ae_false {Action : Type*} [MeasurableSpace Action]
    (p : MeasureTheory.ProbabilityMeasure Action) :
    ¬ (∀ᵐ _a ∂(p : MeasureTheory.Measure Action), False) := by
  intro h
  rw [MeasureTheory.ae_iff] at h
  have hu : {_a : Action | ¬ False} = Set.univ := by ext; simp
  rw [hu] at h
  exact MeasureTheory.IsProbabilityMeasure.ne_zero (p : MeasureTheory.Measure Action)
    (MeasureTheory.Measure.measure_univ_eq_zero.mp h)

/-- The randomized obstruction for completely general probability measures.
No countability or measurability of the acceptable sets is required. -/
theorem measure_randomized_factoring_disjoint_obstruction
    {State Signal Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action) (signal : State → Signal)
    (decision : State → MeasureTheory.ProbabilityMeasure Action)
    (hfactor : FactorsThrough decision signal) {x y : State}
    (hidentified : signal x = signal y)
    (hdisjoint : Disjoint (acceptable x) (acceptable y)) :
    MeasureRandomizedUnacceptableAt acceptable decision x ∨
      MeasureRandomizedUnacceptableAt acceptable decision y := by
  have heq : decision x = decision y := hfactor.eq_of_eq hidentified
  by_cases hx : AlmostSurelyAcceptableAt acceptable decision x
  · right
    intro hy
    unfold AlmostSurelyAcceptableAt at hx hy
    rw [← heq] at hy
    have hb := hx.and hy
    have hf : ∀ᵐ _a ∂(decision x : MeasureTheory.Measure Action), False :=
      hb.mono (fun _a ha => hdisjoint.le_bot ha)
    exact probabilityMeasure_not_ae_false (decision x) hf
  · exact Or.inl hx

/-- Statistic-factorized form of the general probability-measure obstruction. -/
theorem measure_randomized_statistic_rule_disjoint_obstruction
    {State Statistic Action : Type*} [MeasurableSpace Action]
    (acceptable : State → Set Action) (statistic : State → Statistic)
    (rule : Statistic → MeasureTheory.ProbabilityMeasure Action) {x y : State}
    (hidentified : statistic x = statistic y)
    (hdisjoint : Disjoint (acceptable x) (acceptable y)) :
    MeasureRandomizedUnacceptableAt acceptable (rule ∘ statistic) x ∨
      MeasureRandomizedUnacceptableAt acceptable (rule ∘ statistic) y := by
  apply measure_randomized_factoring_disjoint_obstruction acceptable statistic
    (rule ∘ statistic) ⟨rule, rfl⟩ hidentified hdisjoint

end Statistics

/-! ## Set invariance and increment bounds under composition -/

section Composition

/-- Set invariance is closed under composition: if each component maps the
set into itself, so does the composite. -/
theorem invariance_comp {S : Type*} {C : Set S} {f g : S → S}
    (hf : Set.MapsTo f C C) (hg : Set.MapsTo g C C) :
    Set.MapsTo (g ∘ f) C C :=
  hg.comp hf

/-- The same unit increment bound is not closed under composition: two
functions that each move every point by at most one can jointly move a point
by two. -/
theorem increment_bound_not_compositional :
    ∃ f g : ℝ → ℝ,
      (∀ x, |f x - x| ≤ 1) ∧ (∀ x, |g x - x| ≤ 1) ∧
      ∃ x : ℝ, ¬ (|(g ∘ f) x - x| ≤ 1) := by
  refine ⟨fun x => x + 1, fun x => x + 1, fun x => by norm_num,
    fun x => by norm_num, 0, ?_⟩
  norm_num [Function.comp]

/-- Cardinality of the full deterministic state-feedback policy space. This is
a counting identity, not a computational lower bound. -/
theorem card_policySpace (S A : Type*) [Fintype S] [Fintype A] [DecidableEq S] :
    Fintype.card (S → A) = Fintype.card A ^ Fintype.card S :=
  Fintype.card_fun

/-- A point is globally optimal for a natural-valued objective. -/
def IsOptimal {P : Type*} (J : P → ℕ) (p : P) : Prop :=
  ∀ q, J q ≤ J p

/-- Exponential policy-space cardinality alone is not an optimization lower
bound: a constant objective makes every Boolean policy globally optimal. Ported
from the Aristotle target `CapacityCaveat`. -/
theorem exponential_policy_space_with_flat_objective (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n ∧
      ∀ p : Fin n → Bool, IsOptimal (fun _ => 0) p := by
  constructor
  · simp
  · simp [IsOptimal]

/-- For a product of a finite state space and its deterministic policy space,
the separating-response hypothesis yields the explicit lower bound
`|S| * |A| ^ |S|` on the number of realized responses. -/
theorem requisite_variety_augmented {S A R O : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq R] [DecidableEq O]
    (ω : S × (S → A) → R → O) (ρ : S × (S → A) → R)
    (hsep : FiberSeparating ω ρ) (o₀ : O) (hperf : ∀ d, ω d (ρ d) = o₀) :
    Fintype.card S * Fintype.card A ^ Fintype.card S ≤
      (Finset.univ.image ρ).card := by
  have h := requisite_variety_perfect ω ρ hsep o₀ hperf
  rwa [Fintype.card_prod, card_policySpace] at h

/-- Semantic drift: the syntax is fixed while its interpretation changes over
time. -/
def SemanticDrift {W B : Type*} (sem : ℕ → W → B) : Prop :=
  ∃ t x, sem (t + 1) x ≠ sem t x

/-- A finite witness in which one predicate of an interpretation holds at time
zero and fails at time one while the interpreted syntax remains fixed. -/
theorem contract_check_time_indexed :
    ∃ (sem : ℕ → Bool → Bool) (contract : (Bool → Bool) → Prop),
      contract (sem 0) ∧ SemanticDrift sem ∧ ¬contract (sem 1) := by
  refine ⟨fun t => if t = 0 then id else not, fun f => f true = true, ?_, ⟨0, true, ?_⟩, ?_⟩
  · simp
  · simp
  · simp

end Composition

/-! ## Weighted value of observation -/

section ValueInformation

variable {A O : Type*} [Fintype A] [Fintype O] [Nonempty A]

/-- For nonnegative outcome weights, choosing after observing the outcome never
lowers the weighted utility optimum. If the weights sum to one, they may be
read as a predictive distribution. The left side optimizes one action before
the outcome; the right side optimizes an action separately at each outcome. -/
theorem value_of_information_nonneg (u : A → O → ℝ) (w : O → ℝ)
    (hw : ∀ o, 0 ≤ w o) :
    (Finset.univ.sup' Finset.univ_nonempty fun a => ∑ o, w o * u a o) ≤
      ∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o := by
  apply Finset.sup'_le
  intro a _
  apply Finset.sum_le_sum
  intro o _
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun a => u a o) (Finset.mem_univ a))
    (hw o)

/-- Value of information is zero exactly when a single action is optimal
under every outcome the experiment can actually produce.

The support qualification is the whole content of the statement, and it is
where a careless version goes wrong. Quantifying over *every* outcome, rather
than every outcome of positive weight, makes the criterion false: an outcome of
weight zero contributes nothing to either side, so an action that is optimal
everywhere except there still leaves the value of information at zero, while
the unqualified right-hand side fails. `value_of_information_eq_zero_iff` is
the corollary for strictly positive weights, where the qualification can be
dropped because it is vacuous.

Aristotle reached the same qualification independently, from the informal claim
alone, and produced the two-outcome counterexample that forces it. This project
had the side condition too, but paid for it globally, by assuming every outcome
has positive weight; that assumption is not needed and is dropped here. -/
theorem value_of_information_eq_zero_iff_possible (u : A → O → ℝ) (w : O → ℝ)
    (hw : ∀ o, 0 ≤ w o) :
    (Finset.univ.sup' Finset.univ_nonempty fun a => ∑ o, w o * u a o) =
      (∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o)
    ↔ ∃ a : A, ∀ o, 0 < w o → ∀ a' : A, u a' o ≤ u a o := by
  constructor
  · intro heq
    obtain ⟨a₀, -, ha₀⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A))
        (fun a => ∑ o, w o * u a o)
    have hsum : ∑ o, w o * u a₀ o
        = ∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o := by
      rw [← heq]
      exact ha₀.symm
    have hnonneg : ∀ o ∈ (Finset.univ : Finset O),
        0 ≤ w o * ((Finset.univ.sup' Finset.univ_nonempty fun a => u a o) - u a₀ o) := by
      intro o _
      exact mul_nonneg (hw o)
        (sub_nonneg.mpr (Finset.le_sup' (fun a => u a o) (Finset.mem_univ a₀)))
    have hzero :
        ∑ o, w o * ((Finset.univ.sup' Finset.univ_nonempty fun a => u a o) - u a₀ o) = 0 := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← hsum, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    refine ⟨a₀, fun o hpos a' => ?_⟩
    rcases mul_eq_zero.mp (hterm o (Finset.mem_univ o)) with h | h
    · exact absurd h (ne_of_gt hpos)
    · have hs : (Finset.univ.sup' Finset.univ_nonempty fun a => u a o) = u a₀ o :=
        sub_eq_zero.mp h
      calc u a' o ≤ Finset.univ.sup' Finset.univ_nonempty (fun a => u a o) :=
            Finset.le_sup' (fun a => u a o) (Finset.mem_univ a')
        _ = u a₀ o := hs
  · rintro ⟨a, ha⟩
    have hterms : ∀ o ∈ (Finset.univ : Finset O),
        w o * u a o
          = w o * Finset.univ.sup' Finset.univ_nonempty fun a' => u a' o := by
      intro o _
      rcases eq_or_lt_of_le (hw o) with h | h
      · rw [← h]; ring
      · congr 1
        exact (le_antisymm (Finset.sup'_le _ _ fun a' _ => ha o h a')
          (Finset.le_sup' (fun a' => u a' o) (Finset.mem_univ a))).symm
    refine le_antisymm (value_of_information_nonneg u w hw) ?_
    rw [← Finset.sum_congr rfl hterms]
    exact Finset.le_sup' (fun a => ∑ o, w o * u a o) (Finset.mem_univ a)

/-- Under strictly positive weights, the support-qualified equality criterion
reduces to the existence of one action maximizing utility at every outcome. -/
theorem value_of_information_eq_zero_iff (u : A → O → ℝ) (w : O → ℝ)
    (hw : ∀ o, 0 < w o) :
    (Finset.univ.sup' Finset.univ_nonempty fun a => ∑ o, w o * u a o) =
      (∑ o, w o * Finset.univ.sup' Finset.univ_nonempty fun a => u a o)
    ↔ ∃ a : A, ∀ o, ∀ a' : A, u a' o ≤ u a o := by
  rw [value_of_information_eq_zero_iff_possible u w fun o => (hw o).le]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, fun o a' => ha o (hw o) a'⟩,
         fun ⟨a, ha⟩ => ⟨a, fun o _ a' => ha o a'⟩⟩


end ValueInformation

/-! ## The concept lattice of observation support

For the context of states, observations, and possibility-at, mathlib's
complete lattice of formal concepts records the distinctions induced by the
support of the observation channel. Two states have equal observation support
precisely when no formal concept separates them. -/

section ConceptLattice

variable {S O : Type*}

/-- The observation context of a channel: `o` is possible at `s`. -/
def possibleAt (Z : S → PMF O) (s : S) (o : O) : Prop := Z s o ≠ 0

/-- Support equivalence: the channel cannot tell `s` from `s'` even at the
level of which observations are possible at all. -/
def SupportEquiv (Z : S → PMF O) (s s' : S) : Prop :=
  ∀ o, Z s o ≠ 0 ↔ Z s' o ≠ 0

/-- The object concept of a state: the concept generated by it. -/
def objectConcept (r : S → O → Prop) (s : S) : Concept S O r :=
  ⟨lowerPolar r (upperPolar r {s}), upperPolar r {s},
   upperPolar_lowerPolar_upperPolar r {s}, rfl⟩

theorem mem_objectConcept_self (r : S → O → Prop) (s : S) :
    s ∈ (objectConcept r s).extent :=
  subset_lowerPolar_upperPolar r {s} (Set.mem_singleton s)

/-- States are support-equivalent exactly when no formal concept of the
observation context separates them. -/
theorem supportEquiv_iff_no_concept_separates (Z : S → PMF O) (s s' : S) :
    SupportEquiv Z s s' ↔
      ∀ c : Concept S O (possibleAt Z), s ∈ c.extent ↔ s' ∈ c.extent := by
  constructor
  · intro h c
    have hmem : ∀ x : S, x ∈ c.extent ↔ ∀ ⦃o⦄, o ∈ c.intent → possibleAt Z x o := by
      intro x
      conv_lhs => rw [← c.lowerPolar_intent]
      exact Iff.rfl
    rw [hmem s, hmem s']
    constructor
    · intro hx o ho
      exact (h o).mp (hx ho)
    · intro hx o ho
      exact (h o).mpr (hx ho)
  · intro h o
    have hs' : s' ∈ (objectConcept (possibleAt Z) s).extent :=
      (h _).mp (mem_objectConcept_self _ _)
    have hs : s ∈ (objectConcept (possibleAt Z) s').extent :=
      (h _).mpr (mem_objectConcept_self _ _)
    constructor
    · intro hzs
      exact hs' ((mem_upperPolar_singleton _).mpr hzs)
    · intro hzs'
      exact hs ((mem_upperPolar_singleton _).mpr hzs')

end ConceptLattice

end

end HardProblems


/-! Inlined dependency: LeanTest/HardProblems/InformationOrder.lean -/


/-!
# Deterministic information preorder and decision relevance

An observation or representation is modeled here only as a map from states to
reported values. Its information content is the partition of states induced
by equality of reports. Post-processing can merge partition cells but cannot
separate states that the original report identified.

The decision consequence is explicit. An action is robust at the current
report when it is acceptable at every state compatible with that report. A
finer experiment has smaller compatibility classes and therefore weakly more
robust actions. A finite example makes this inclusion strict when a quotient
erases a distinction on which the acceptable action depends.

These are deterministic partition and order results. They do not define
entropy, mutual information, statistical sufficiency, or a stochastic data
processing inequality.
-/

namespace HardProblems
namespace InformationOrder

universe u v w z

/-- States are indistinguishable under an observation map when they produce
the same report. -/
def Indist {S : Type u} {O : Type v} (observe : S → O) (x y : S) : Prop :=
  observe x = observe y

/-- Equality of reports induces an equivalence relation on states. -/
theorem indist_equivalence {S : Type u} {O : Type v} (observe : S → O) :
    Equivalence (Indist observe) where
  refl _ := rfl
  symm h := h.symm
  trans hxy hyz := hxy.trans hyz

/-- `fine` refines `coarse` when the coarse report is obtained by deterministic
post-processing of the fine report. This orients the existing
`HardProblems.FactorsThrough` relation as an information preorder; it does not
introduce a second notion of factorization. -/
def ExperimentRefines {S : Type u} {F : Type v} {C : Type w}
    (fine : S → F) (coarse : S → C) : Prop :=
  FactorsThrough coarse fine

/-- Every experiment refines itself. -/
theorem experimentRefines_refl {S : Type u} {O : Type v}
    (observe : S → O) : ExperimentRefines observe observe := by
  exact ⟨id, by funext x; rfl⟩

/-- Deterministic experiment refinement is transitive. -/
theorem experimentRefines_trans {S : Type u} {A : Type v} {B : Type w}
    {C : Type z} {first : S → A} {second : S → B} {third : S → C}
    (h₁ : ExperimentRefines first second)
    (h₂ : ExperimentRefines second third) :
    ExperimentRefines first third := by
  rcases h₁ with ⟨post₁, rfl⟩
  rcases h₂ with ⟨post₂, rfl⟩
  exact ⟨post₂ ∘ post₁, by funext x; rfl⟩

/-- Refinement reverses inclusion of indistinguishability classes: equality of
fine reports forces equality of coarse reports. -/
theorem ExperimentRefines.indist {S : Type u} {F : Type v} {C : Type w}
    {fine : S → F} {coarse : S → C}
    (h : ExperimentRefines fine coarse) {x y : S}
    (hxy : Indist fine x y) : Indist coarse x y := by
  exact (show FactorsThrough coarse fine from h).eq_of_eq hxy

/-- Actions acceptable at every state compatible with the current report.
The acceptable-action predicate is part of the task, rather than part of the
observation alone. -/
def RobustActions {S : Type u} {O : Type v} {A : Type w}
    (observe : S → O) (Acceptable : S → A → Prop) (x : S) : Set A :=
  {a | ∀ y, Indist observe x y → Acceptable y a}

/-- A finer experiment weakly enlarges the set of robust acceptable actions.
The result is task-relevant but deterministic: it compares compatibility
classes, not probabilities or average information. -/
theorem ExperimentRefines.robustActions_mono
    {S : Type u} {F : Type v} {C : Type w} {A : Type z}
    {fine : S → F} {coarse : S → C}
    (h : ExperimentRefines fine coarse) (Acceptable : S → A → Prop) (x : S) :
    RobustActions coarse Acceptable x ⊆ RobustActions fine Acceptable x := by
  intro a ha y hxy
  exact ha y (h.indist hxy)

/-- Mutual deterministic factorization gives exactly the same induced
indistinguishability relation. The report types and report values themselves
need not be equal. -/
theorem indist_iff_of_mutual_refinement
    {S : Type u} {O₁ : Type v} {O₂ : Type w}
    {first : S → O₁} {second : S → O₂}
    (h₁₂ : ExperimentRefines first second)
    (h₂₁ : ExperimentRefines second first) (x y : S) :
    Indist first x y ↔ Indist second x y :=
  ⟨h₁₂.indist, h₂₁.indist⟩

/-- Mutual deterministic factorization preserves every robust action set for
every task predicate. -/
theorem robustActions_eq_of_mutual_refinement
    {S : Type u} {O₁ : Type v} {O₂ : Type w} {A : Type z}
    {first : S → O₁} {second : S → O₂}
    (h₁₂ : ExperimentRefines first second)
    (h₂₁ : ExperimentRefines second first)
    (Acceptable : S → A → Prop) (x : S) :
    RobustActions first Acceptable x = RobustActions second Acceptable x := by
  apply Set.Subset.antisymm
  · exact h₂₁.robustActions_mono Acceptable x
  · exact h₁₂.robustActions_mono Acceptable x

/-- A strict finite decision loss. The identity experiment separates the two
Bool states, while the quotient to `Unit` merges them. An action is acceptable
exactly when it names the true state. At state `false`, the fine report permits
the robust action `false`; the coarse report permits no robust action. -/
theorem quotient_strict_decision_loss :
    let fine : Bool → Bool := id
    let coarse : Bool → Unit := fun _ ↦ ()
    let Acceptable : Bool → Bool → Prop := fun state action ↦ state = action
    ExperimentRefines fine coarse ∧
      ¬ Indist fine false true ∧ Indist coarse false true ∧
      RobustActions coarse Acceptable false = ∅ ∧
      RobustActions fine Acceptable false = {false} ∧
      RobustActions coarse Acceptable false ⊂
        RobustActions fine Acceptable false := by
  dsimp
  refine ⟨⟨fun _ ↦ (), rfl⟩, by simp [Indist], by simp [Indist], ?_⟩
  have hCoarse : RobustActions (fun _ : Bool ↦ ())
      (fun state action : Bool ↦ state = action) false = ∅ := by
    ext action
    constructor
    · intro ha
      have hFalse := ha false (by rfl)
      have hTrue := ha true (by rfl)
      simp only [Set.mem_empty_iff_false]
      cases action <;> simp_all
    · simp
  have hFine : RobustActions id
      (fun state action : Bool ↦ state = action) false = {false} := by
    ext action
    simp [RobustActions, Indist]
  refine ⟨hCoarse, hFine, ?_⟩
  rw [hCoarse, hFine]
  exact Set.empty_ssubset.mpr (Set.singleton_nonempty false)

end InformationOrder
end HardProblems


/-! Inlined dependency: LeanTest/HardProblems/Behavioral.lean -/


/-!
# Behavioral systems, hiding, gluing, and safety

This module formalizes a deliberately small fragment of behavioral systems
theory. A behavior is a set of trajectories on one declared signal boundary.
Interconnection is intersection only after that boundary has been aligned.
Hiding is direct image under a pointwise signal map. Local gluing concerns
ordinary functions on two overlapping time domains. Safety is universal over
the admitted behavior and may therefore hold vacuously when that behavior is
empty. The repo-only viability declarations at the end make that separation
explicit: the empty behavior is safe for every predicate but is not viable.

The declarations were first submitted as an Aristotle proof target pinned to
Lean and mathlib v4.28.0. The proofs below are checked on the repository's
v4.33.0-rc1 toolchain.
-/

namespace HardProblems
namespace Behavioral

universe u v w

/-- A complete signal trajectory on time domain `T`. -/
abbrev Trajectory (T : Type u) (W : Type v) := T → W

/-- A behavior is the set of trajectories admitted by a system model. -/
abbrev Behavior (T : Type u) (W : Type v) := Set (Trajectory T W)

/-- Apply a signal map pointwise to a trajectory. -/
def mapTrajectory {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (x : Trajectory T W) : Trajectory T V :=
  f ∘ x

/-- Hide or relabel signal coordinates by taking the direct image of a
behavior under the pointwise signal map. -/
def hide {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B : Behavior T W) : Behavior T V :=
  mapTrajectory f '' B

/-- On one already aligned signal boundary, behavioral interconnection imposes
both component constraints. -/
def interconnect {T : Type u} {W : Type v}
    (B₁ B₂ : Behavior T W) : Behavior T W :=
  B₁ ∩ B₂

/-- Hiding after interconnection is contained in interconnecting after hiding.
The reverse inclusion can fail because the two projected witnesses need not be
the same hidden trajectory. -/
theorem hide_interconnect_subset {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B₁ B₂ : Behavior T W) :
    hide f (interconnect B₁ B₂) ⊆
      interconnect (hide f B₁) (hide f B₂) := by
  rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
  exact ⟨⟨x, hx₁, rfl⟩, ⟨x, hx₂, rfl⟩⟩

/-- Explicit strictness witness: each component admits a different hidden Bool
trajectory with the same visible projection. The components are individually
viable, their interconnection is empty, but their visible projections have a
nonempty interconnection. -/
theorem hide_interconnect_strict_counterexample :
    let f : Bool × Bool → Bool := Prod.fst
    let x₀ : Trajectory Unit (Bool × Bool) := fun _ ↦ (false, false)
    let x₁ : Trajectory Unit (Bool × Bool) := fun _ ↦ (false, true)
    let B₀ : Behavior Unit (Bool × Bool) := {x₀}
    let B₁ : Behavior Unit (Bool × Bool) := {x₁}
    B₀.Nonempty ∧ B₁.Nonempty ∧ interconnect B₀ B₁ = ∅ ∧
      hide f (interconnect B₀ B₁) ⊂
        interconnect (hide f B₀) (hide f B₁) := by
  dsimp
  refine ⟨Set.singleton_nonempty _, Set.singleton_nonempty _, ?_⟩
  have hEmpty :
      interconnect ({fun _ : Unit ↦ (false, false)} :
        Behavior Unit (Bool × Bool)) {fun _ : Unit ↦ (false, true)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz₀, hz₁⟩
    rw [Set.mem_singleton_iff] at hz₀ hz₁
    have hEq : (fun _ : Unit ↦ (false, false)) =
        fun _ : Unit ↦ (false, true) := hz₀.symm.trans hz₁
    have := congrFun hEq ()
    simp at this
  refine ⟨hEmpty, ?_⟩
  refine Set.ssubset_iff_subset_ne.mpr
    ⟨hide_interconnect_subset _ _ _, ?_⟩
  intro hEq
  have hVisible : (fun _ : Unit ↦ false) ∈
      interconnect
        (hide Prod.fst ({fun _ : Unit ↦ (false, false)} :
          Behavior Unit (Bool × Bool)))
        (hide Prod.fst ({fun _ : Unit ↦ (false, true)} :
          Behavior Unit (Bool × Bool))) := by
    exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  have hImpossible : (fun _ : Unit ↦ false) ∈
      hide Prod.fst
        (interconnect ({fun _ : Unit ↦ (false, false)} :
          Behavior Unit (Bool × Bool)) {fun _ : Unit ↦ (false, true)}) := by
    rw [hEq]
    exact hVisible
  rw [hEmpty] at hImpossible
  rcases hImpossible with ⟨_, hmem, _⟩
  exact hmem

/-- Exact relabeling by an equivalence loses no behavior. -/
theorem hide_equiv_symm {T : Type u} {W : Type v} {V : Type w}
    (e : W ≃ V) (B : Behavior T W) :
    hide e.symm (hide e B) = B := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzx⟩
    have hzx' : z = x := by
      simpa [mapTrajectory, Function.comp_def] using hzx
    simpa [← hzx'] using hz
  · intro hx
    refine ⟨mapTrajectory e x, ⟨x, hx, rfl⟩, ?_⟩
    funext t
    simp [mapTrajectory, Function.comp_def]

/-- A temporal safety predicate holds at every time on every admitted
trajectory. -/
def IsSafe {T : Type u} {W : Type v}
    (B : Behavior T W) (Safe : W → Prop) : Prop :=
  ∀ x ∈ B, ∀ t, Safe (x t)

/-- Refining a behavior preserves every universal safety property. -/
theorem isSafe_mono {T : Type u} {W : Type v}
    {B B' : Behavior T W} {Safe : W → Prop}
    (hsub : B' ⊆ B) (h : IsSafe B Safe) : IsSafe B' Safe := by
  intro x hx t
  exact h x (hsub hx) t

/-- Direct-image hiding has an exact safety semantics: a visible predicate
holds on every projected trajectory exactly when its pullback holds on every
original trajectory. This says nothing about predicates on discarded signal
coordinates. -/
theorem isSafe_hide_iff {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B : Behavior T W) (SafeV : V → Prop) :
    IsSafe (hide f B) SafeV ↔ IsSafe B (SafeV ∘ f) := by
  constructor
  · intro h x hx t
    simpa [mapTrajectory, Function.comp_def] using
      h (mapTrajectory f x) ⟨x, hx, rfl⟩ t
  · rintro h _ ⟨x, hx, rfl⟩ t
    simpa [mapTrajectory, Function.comp_def] using h x hx t

/-- Hiding preserves a safety property only when the signal map carries the
declared internal safe set into the external one. -/
theorem isSafe_hide {T : Type u} {W : Type v} {V : Type w}
    {B : Behavior T W} {SafeW : W → Prop} {SafeV : V → Prop}
    (f : W → V) (hB : IsSafe B SafeW)
    (hmap : ∀ w, SafeW w → SafeV (f w)) :
    IsSafe (hide f B) SafeV := by
  rintro _ ⟨x, hx, rfl⟩ t
  exact hmap (x t) (hB x hx t)

/-- A discrete trajectory follows `step` at every successor time. -/
def IsRun {S : Type u} (step : S → S) (x : Trajectory ℕ S) : Prop :=
  ∀ n, x (n + 1) = step (x n)

/-- All runs whose initial state lies in `Init`. -/
def generatedBehavior {S : Type u} (step : S → S) (Init : Set S) :
    Behavior ℕ S :=
  {x | x 0 ∈ Init ∧ IsRun step x}

/-- Forward invariance gives all-time safety for every generated run. -/
theorem generatedBehavior_safe_of_invariant {S : Type u}
    {step : S → S} {Init Safe : Set S}
    (hInit : Init ⊆ Safe) (hInv : Set.MapsTo step Safe Safe) :
    IsSafe (generatedBehavior step Init) Safe := by
  rintro x ⟨hx₀, hrun⟩ n
  induction n with
  | zero => exact hInit hx₀
  | succ n ih =>
      rw [hrun n]
      exact hInv ih

/-- For the behavior generated from every state in `Safe`, temporal safety is
equivalent to one-step forward invariance. -/
theorem generatedBehavior_safe_iff_invariant {S : Type u}
    (step : S → S) (Safe : Set S) :
    IsSafe (generatedBehavior step Safe) Safe ↔
      Set.MapsTo step Safe Safe := by
  constructor
  · intro h s hs
    let x : Trajectory ℕ S := fun n ↦ Nat.rec s (fun _ current ↦ step current) n
    have hrun : IsRun step x := by
      intro n
      simp [x]
    have hx : x ∈ generatedBehavior step Safe := by
      exact ⟨by simpa [x] using hs, hrun⟩
    have hs₁ := h x hx 1
    change x 1 ∈ Safe at hs₁
    simpa [x] using hs₁
  · intro hInv
    exact generatedBehavior_safe_of_invariant (by exact fun _ h ↦ h) hInv

/-! ## Binary local gluing

This is the function-level gluing mechanism behind a sheaf semantics. It does
not assert that an arbitrary assignment of admissible local behaviors is a
sheaf; closure of admissibility under restriction and gluing is extra data.
-/

/-- Restrict a local trajectory from `I` to a smaller time domain `J`. -/
def restrict {T : Type u} {W : Type v} {I J : Set T}
    (hJI : J ⊆ I) (x : I → W) : J → W :=
  fun t ↦ x ⟨t.1, hJI t.2⟩

/-- Two local trajectories agree wherever their time domains overlap. -/
def Compatible {T : Type u} {W : Type v} {I J : Set T}
    (x : I → W) (y : J → W) : Prop :=
  ∀ (t : T) (htI : t ∈ I) (htJ : t ∈ J),
    x ⟨t, htI⟩ = y ⟨t, htJ⟩

/-- Compatible functions on two time domains have a unique global function on
their union with the prescribed restrictions. -/
theorem existsUnique_glue {T : Type u} {W : Type v} {I J : Set T}
    (x : I → W) (y : J → W) (hxy : Compatible x y) :
    ∃! z : ↥(I ∪ J) → W,
      restrict Set.subset_union_left z = x ∧
      restrict Set.subset_union_right z = y := by
  classical
  let z : ↥(I ∪ J) → W := fun t ↦
    if htI : (t : T) ∈ I then x ⟨t, htI⟩
    else y ⟨t, t.property.resolve_left htI⟩
  have hzI : restrict Set.subset_union_left z = x := by
    funext t
    simp [restrict, z]
  have hzJ : restrict Set.subset_union_right z = y := by
    funext t
    by_cases htI : (t : T) ∈ I
    · simpa [restrict, z, htI] using hxy t htI t.property
    · simp [restrict, z, htI]
  refine ⟨z, ⟨hzI, hzJ⟩, ?_⟩
  intro z' hz'
  funext t
  by_cases htI : (t : T) ∈ I
  · have h := congrFun hz'.1 (⟨t, htI⟩ : I)
    simpa [restrict, z, htI] using h
  · have htJ : (t : T) ∈ J := t.property.resolve_left htI
    have h := congrFun hz'.2 (⟨t, htJ⟩ : J)
    simpa [restrict, z, htI] using h

/-- Raw compatible functions glue, but a nonempty declared set of admissible
global trajectories need not contain that glue. Thus arbitrary local/global
admissibility data do not acquire the sheaf property for free. -/
theorem admissible_glue_counterexample :
    let I : Set Bool := {false}
    let J : Set Bool := {true}
    let x : I → Bool := fun _ ↦ false
    let y : J → Bool := fun _ ↦ true
    let G : Set (↥(I ∪ J) → Bool) := {fun _ ↦ false}
    Compatible x y ∧ G.Nonempty ∧
      ¬ ∃ z ∈ G,
        restrict Set.subset_union_left z = x ∧
        restrict Set.subset_union_right z = y := by
  dsimp
  refine ⟨?_, Set.singleton_nonempty _, ?_⟩
  · intro t htI htJ
    rw [Set.mem_singleton_iff] at htI htJ
    exact Bool.noConfusion (htI.symm.trans htJ)
  · rintro ⟨z, hz, ⟨_, hzJ⟩⟩
    subst z
    have h := congrFun hzJ (⟨true, by simp⟩ : (↑({true} : Set Bool)))
    simp [restrict] at h

/-! ## Viability boundary

These declarations are intentionally separate from universal safety. They were
added in the repository after the pinned Aristotle target was submitted.
-/

/-- A behavior is viable when it admits at least one trajectory. -/
def IsViable {T : Type u} {W : Type v} (B : Behavior T W) : Prop :=
  B.Nonempty

/-- Universal safety is vacuous on the empty behavior. -/
theorem empty_behavior_safe {T : Type u} {W : Type v} {Safe : W → Prop} :
    IsSafe (∅ : Behavior T W) Safe := by
  simp [IsSafe]

/-- The empty behavior is not viable. -/
theorem empty_behavior_not_viable {T : Type u} {W : Type v} :
    ¬ IsViable (∅ : Behavior T W) := by
  simp [IsViable]

end Behavioral
end HardProblems


/-! Target module: LeanTest/HardProblems/BoundaryClosures.lean -/


/-!
# Boundaries as closure operators

Aristotle-verified unification, ported from mathlib v4.28. Each declared
boundary induces a closure operator in mathlib's standard sense on a poset of
possibilities, and two recurring results of the book become one statement
each.

* The negative results are idempotence. Adding a `Programmed` transformation
  leaves `reachSet` fixed; post-processing an observation report leaves the
  `Indist` saturation fixed.
* The positive results are strict enlargement, with concrete finite
  witnesses, not existence by choice.

Where the unification stops, proved rather than smoothed over:

* Hiding does not commute with interconnection. The behavioral closure exists,
  but it is not a lattice homomorphism (`hide_interconnect_subset_and_strict`).
* A fibrewise closure need not commute with reindexing
  (`reindex_closure_need_not_commute`), which is the closure-operator face of
  `FibredOrder.ambient_preimage_can_be_unrealized`: a difficulty claim does
  not transport between contexts without a commuting condition.

The definitions duplicated under `ClosureUnification` are verbatim copies of
`Reach`, `Programmed`, `Indist`, `RobustActions`, `Behavior`, `interconnect`,
and `hide` from their home modules, kept so this module's statements are
self-contained; the agreement lemmas at the end
of this file pin each used copy to its original, so the copies cannot drift.
-/

universe u v w

namespace HardProblems
namespace ClosureUnification

/-! ## Fixed data from the project. Do not modify. -/

/-- Reachability under a set of primitive transformations. -/
inductive Reach {X : Type u} (G : Set (X → X)) (x : X) : X → Prop
  | refl : Reach G x x
  | tail : ∀ {y z : X} {g : X → X}, Reach G x y → g ∈ G → z = g y → Reach G x z

/-- A transformation already realizable pointwise from the existing primitives. -/
def Programmed {X : Type u} (G : Set (X → X)) (g : X → X) : Prop :=
  ∀ y : X, Reach G y (g y)

/-- States an observation map cannot separate. -/
def Indist {S : Type u} {O : Type v} (observe : S → O) (x y : S) : Prop :=
  observe x = observe y

/-- Actions acceptable at every state compatible with the current report. -/
def RobustActions {S : Type u} {O : Type v} {A : Type w}
    (observe : S → O) (Acceptable : S → A → Prop) (x : S) : Set A :=
  {a | ∀ y, Indist observe x y → Acceptable y a}

/-- A behavior is a set of admissible trajectories. -/
abbrev Behavior (T : Type u) (W : Type v) := Set (T → W)

/-- Interconnection removes trajectories. -/
def interconnect {T : Type u} {W : Type v} (B₁ B₂ : Behavior T W) : Behavior T W :=
  B₁ ∩ B₂

/-- Hiding identifies trajectories along a signal projection. -/
def hide {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B : Behavior T W) : Behavior T V :=
  (fun w => f ∘ w) '' B

/-! ## Goal 1: reachability is a closure operator

The reachable-set map on `Set X` should be extensive, monotone, and idempotent.
This is the cleanest instance and the one most likely to go through. -/

/-- The set of states reachable from a set of starting states. -/
def reachSet {X : Type u} (G : Set (X → X)) (S : Set X) : Set X :=
  {z | ∃ x ∈ S, Reach G x z}

lemma Reach.trans {X : Type u} {G : Set (X → X)} {x y z : X}
    (hxy : Reach G x y) (hyz : Reach G y z) : Reach G x z := by
  induction hyz with
  | refl => exact hxy
  | tail hy hmem hz ih =>
      subst hz
      exact .tail ih hmem rfl

/-- Goal 1. `reachSet G` is a closure operator on `Set X`. -/
def reachClosure {X : Type u} (G : Set (X → X)) : ClosureOperator (Set X) where
  toFun := reachSet G
  monotone' := by
    intro S T hST z hz
    rcases hz with ⟨x, hxS, hxz⟩
    exact ⟨x, hST hxS, hxz⟩
  le_closure' := by
    intro S x hx
    exact ⟨x, hx, .refl⟩
  idempotent' := by
    intro S
    apply Set.Subset.antisymm
    · rintro z ⟨y, ⟨x, hx, hxy⟩, hyz⟩
      exact ⟨x, hx, hxy.trans hyz⟩
    · rintro z hz
      exact ⟨z, hz, .refl⟩

/-! ## Goal 2: the negative results are idempotence

Adding a transformation already programmed from `G` does not enlarge the
closure. This should follow from idempotence rather than being proved again
from scratch; if it cannot, say why. -/

lemma Reach.insert_programmed {X : Type u} {G : Set (X → X)} {g : X → X}
    (hg : Programmed G g) {x z : X} (h : Reach (insert g G) x z) : Reach G x z := by
  induction h with
  | refl => exact .refl
  | tail hstep hmem hz ih =>
      subst hz
      rcases hmem with rfl | hmem
      · exact ih.trans (hg _)
      · exact .tail ih hmem rfl

/-- Goal 2. A programmed transformation adds no reachability. -/
theorem reachSet_insert_programmed {X : Type u} (G : Set (X → X))
    {g : X → X} (hg : Programmed G g) (S : Set X) :
    reachSet (insert g G) S = reachSet G S := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, hreach⟩
    exact ⟨x, hx, hreach.insert_programmed hg⟩
  · rintro z ⟨x, hx, hreach⟩
    exact ⟨x, hx, by
      induction hreach with
      | refl => exact .refl
      | tail hstep hmem hz ih => exact .tail ih (Set.mem_insert_of_mem _ hmem) hz⟩

/-! ## Goal 3: the positive results are strict enlargement

A genuinely new primitive can strictly enlarge the closure. Give an explicit
witness, not an existence claim discharged by choice. -/

/-- Goal 3. The concrete two-state system `Bool`, with no old primitives,
initial state `false`, and the new constant-`true` primitive, strictly enlarges
reachable closure. -/
theorem exists_strict_enlargement :
    ∃ (X : Type) (G : Set (X → X)) (g : X → X) (S : Set X),
      reachSet G S ⊂ reachSet (insert g G) S := by
  refine ⟨Bool, ∅, (fun _ => true), {false}, ?_⟩
  constructor
  · rintro z ⟨x, hx, hreach⟩
    exact ⟨x, hx, by
      induction hreach with
      | refl => exact .refl
      | tail hstep hmem hz => exact False.elim hmem⟩
  · intro hreverse
    have htrue : true ∈ reachSet (insert (fun _ : Bool => true) ∅) {false} :=
      ⟨false, by simp,
        Reach.tail (g := fun _ : Bool => true) Reach.refl (by simp) rfl⟩
    have hold : true ∈ reachSet (∅ : Set (Bool → Bool)) {false} := hreverse htrue
    rcases hold with ⟨x, hx, hreach⟩
    have hxfalse : x = false := by simpa using hx
    subst x
    have hempty : ∀ z : Bool, Reach (∅ : Set (Bool → Bool)) false z → z = false := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail hstep hmem heq => exact False.elim hmem
    have : true = false := hempty true hreach
    cases this

/-! ## Goal 4: the information boundary is the same shape

`RobustActions` is an intersection over an equivalence class, so the induced
operator on the state side should also be a closure. Determine the right
carrier: the natural candidate is saturation of a set of states under `Indist`.
State and prove the correct one. -/

/-- Saturation of states under equality of observations. -/
def indistSaturation {S : Type u} {O : Type v} (observe : S → O)
    (T : Set S) : Set S :=
  {y | ∃ x ∈ T, Indist observe x y}

/-- Goal 4. Saturation under observational indistinguishability is a closure
operator on `Set S`. -/
def indistClosure {S : Type u} {O : Type v} (observe : S → O) :
    ClosureOperator (Set S) where
  toFun := indistSaturation observe
  monotone' := by
    rintro A B h y ⟨x, hx, hxy⟩
    exact ⟨x, h hx, hxy⟩
  le_closure' := by
    intro A x hx
    exact ⟨x, hx, rfl⟩
  idempotent' := by
    intro A
    apply Set.Subset.antisymm
    · rintro y ⟨x, ⟨z, hz, hzx⟩, hxy⟩
      exact ⟨z, hz, hzx.trans hxy⟩
    · intro y hy
      exact ⟨y, hy, rfl⟩

/-- Goal 4'. If `coarse = k ∘ fine`, fine observational saturation is contained
in coarse observational saturation: a finer experiment separates at least as
many states. -/
theorem indistClosure_le_of_refines {S : Type u} {F : Type v} {Cc : Type w}
    (fine : S → F) (coarse : S → Cc) (k : F → Cc) (hk : coarse = k ∘ fine) :
    ∀ T : Set S, indistClosure fine T ⊆ indistClosure coarse T := by
  intro T y hy
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨x, hx, ?_⟩
  show coarse x = coarse y
  rw [hk]
  exact congrArg k hxy

/-! ## Goal 5: where the analogy breaks

Direct image (hiding) does not preserve interconnection. Its composite with the
right adjoint, inverse image, is nevertheless the standard saturation closure.
-/

/-- Pulling a hidden behavior back along the trajectory projection gives a
closure operator on behaviors. -/
def behavioralClosure {T : Type u} {W : Type v} {V : Type w} (f : W → V) :
    ClosureOperator (Behavior T W) where
  toFun B := {w | f ∘ w ∈ hide f B}
  monotone' := by
    rintro B C h w ⟨w', hw', heq⟩
    exact ⟨w', h hw', heq⟩
  le_closure' := by
    intro B w hw
    exact ⟨w, hw, rfl⟩
  idempotent' := by
    intro B
    apply Set.Subset.antisymm
    · rintro w ⟨w', ⟨w'', hw'', heq'⟩, heq⟩
      exact ⟨w'', hw'', heq'.trans heq⟩
    · intro w hw
      exact ⟨w, hw, rfl⟩

/-- Goal 5. Hiding after interconnection is always contained in interconnecting
after hiding. The displayed `Bool`/`Unit` example makes this inclusion strict,
so hiding is not a meet (lattice) homomorphism. -/
theorem hide_interconnect_subset_and_strict :
    (∀ {T W V : Type} (f : W → V) (B₁ B₂ : Behavior T W),
      hide f (interconnect B₁ B₂) ⊆ interconnect (hide f B₁) (hide f B₂)) ∧
    (let B₁ : Behavior Unit Bool := {w | w () = false}
     let B₂ : Behavior Unit Bool := {w | w () = true}
     hide (fun _ : Bool => ()) (interconnect B₁ B₂) ⊂
       interconnect (hide (fun _ : Bool => ()) B₁)
         (hide (fun _ : Bool => ()) B₂)) := by
  constructor
  · intro T W V f B₁ B₂ v hv
    rcases hv with ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
    exact ⟨⟨w, hw₁, rfl⟩, ⟨w, hw₂, rfl⟩⟩
  · dsimp
    constructor
    · intro v hv
      rcases hv with ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
      exact ⟨⟨w, hw₁, rfl⟩, ⟨w, hw₂, rfl⟩⟩
    · intro hreverse
      let v : Unit → Unit := fun _ => ()
      have hv : v ∈ interconnect
          (hide (fun _ : Bool => ()) {w : Unit → Bool | w () = false})
          (hide (fun _ : Bool => ()) {w : Unit → Bool | w () = true}) := by
        constructor
        · exact ⟨(fun _ => false), rfl, rfl⟩
        · exact ⟨(fun _ => true), rfl, rfl⟩
      have hv' := hreverse hv
      rcases hv' with ⟨w, ⟨hwf, hwt⟩, _⟩
      simp only [Set.mem_setOf_eq] at hwf hwt
      rw [hwf] at hwt
      contradiction

/-! ## Goal 6: fibrewise closure and reindexing

The condition is an equality of the two composites. It is extra structure and
does not follow merely from having closure operators in the fibers. -/

/-- A reindexing order homomorphism commutes with two fiberwise closures when
the two possible composites agree pointwise. -/
def ReindexCommutes {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (r : Q →o P) (cQ : ClosureOperator Q) (cP : ClosureOperator P) : Prop :=
  ∀ x, r (cQ x) = cP (r x)

/-- The closure on `Set Bool` that adjoins `false`. -/
def addFalseClosure : ClosureOperator (Set Bool) where
  toFun S := S ∪ {false}
  monotone' := by
    intro A B h x hx
    exact hx.elim (fun hxA => Or.inl (h hxA)) Or.inr
  le_closure' := by
    intro A x hx
    exact Or.inl hx
  idempotent' := by
    intro A
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto

/-- Reindexing by inverse image along the map `Unit → Bool` selecting `false`
does not commute with `addFalseClosure` and the identity closure on `Set Unit`.
Both carriers are nonempty, nontrivial finite posets. -/
theorem reindex_closure_need_not_commute :
    let r : Set Bool →o Set Unit :=
      { toFun := Set.preimage (fun _ : Unit => false)
        monotone' := by intro A B h; exact Set.preimage_mono h }
    ¬ ReindexCommutes r addFalseClosure (ClosureOperator.id (Set Unit)) := by
  intro r h
  have heq := h (∅ : Set Bool)
  have hunit : () ∈ r (addFalseClosure (∅ : Set Bool)) := Or.inr rfl
  rw [heq] at hunit
  exact hunit


/-! ## The copies cannot drift from the originals -/

/-- The local `Reach` is the project's `Reach`, definitionally. -/
theorem reach_agrees {X : Type u} (G : Set (X → X)) (x z : X) :
    ClosureUnification.Reach G x z ↔ HardProblems.Reach G x z := by
  constructor
  · intro h
    induction h with
    | refl => exact HardProblems.Reach.refl
    | tail hxy hg hz ih => exact HardProblems.Reach.tail ih hg hz
  · intro h
    induction h with
    | refl => exact ClosureUnification.Reach.refl
    | tail hxy hg hz ih => exact ClosureUnification.Reach.tail ih hg hz

/-- The local `Indist` is `InformationOrder.Indist`, definitionally. -/
theorem indist_agrees {S : Type u} {O : Type v} (observe : S → O) (x y : S) :
    ClosureUnification.Indist observe x y ↔
      InformationOrder.Indist observe x y :=
  Iff.rfl

/-- The local `hide` is `Behavioral.hide`, definitionally. -/
theorem hide_agrees {T : Type u} {W : Type v} {V : Type w}
    (f : W → V) (B : ClosureUnification.Behavior T W) :
    ClosureUnification.hide f B = Behavioral.hide f B := by
  rfl

/-- The local `Programmed` is the project's `Programmed`: both quantify the
respective `Reach`, and `reach_agrees` bridges those. -/
theorem programmed_agrees {X : Type u} (G : Set (X → X)) (g : X → X) :
    ClosureUnification.Programmed G g ↔ HardProblems.Programmed G g := by
  constructor
  · intro h y
    exact (reach_agrees G y (g y)).mp (h y)
  · intro h y
    exact (reach_agrees G y (g y)).mpr (h y)

/-- The local `RobustActions` is `InformationOrder.RobustActions`,
definitionally. -/
theorem robustActions_agrees {S : Type u} {O : Type v} {A : Type w}
    (observe : S → O) (Acceptable : S → A → Prop) (x : S) :
    ClosureUnification.RobustActions observe Acceptable x =
      InformationOrder.RobustActions observe Acceptable x :=
  rfl

/-- The local `interconnect` is `Behavioral.interconnect`, definitionally. -/
theorem interconnect_agrees {T : Type u} {W : Type v}
    (B₁ B₂ : ClosureUnification.Behavior T W) :
    ClosureUnification.interconnect B₁ B₂ = Behavioral.interconnect B₁ B₂ :=
  rfl

/-- The strict enlargement of Goal 3, restated with its witness in the
statement rather than behind an existential: adjoining the constant-`true`
move to the empty move set strictly enlarges what is reachable from
`{false}`. -/
theorem reachSet_insert_const_true_strict :
    reachSet (∅ : Set (Bool → Bool)) {false} ⊂
      reachSet (insert (fun _ => true) (∅ : Set (Bool → Bool))) {false} := by
  constructor
  · rintro z ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    induction h with
    | refl => exact Reach.refl
    | tail _ hg hz ih => exact Reach.tail ih (Set.mem_insert_of_mem _ hg) hz
  · intro hrev
    have htrue : true ∈
        reachSet (insert (fun _ => true) (∅ : Set (Bool → Bool))) {false} :=
      ⟨false, rfl, Reach.tail Reach.refl (Set.mem_insert _ _) rfl⟩
    rcases hrev htrue with ⟨x, hx, h⟩
    cases h with
    | refl => simp at hx
    | tail _ hg _ => simp at hg

end ClosureUnification
end HardProblems
