import Mathlib

/-!
This snippet is about:

  PathBetween
  barrier
  exists_dip_of_barrier_pos
  barrier_eq_top_of_no_path
  barrier_eq_zero_of_monotone_path
  barrier_lt_iff
  pathBetween_shortcut_nonempty_iff
  barrier_shortcut_eq
  exists_shortcut_hiding_valley

found at line 524 of 534, near the end of this file.

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


/-! Target module: LeanTest/HardProblems/Ruggedness.lean -/


/-!
# Directed paths and barrier heights

This module gives graph-level definitions of finite paths, local maxima, and
barriers. A positive barrier forces a dip below the starting value on every
path. An empty path family gives barrier `⊤`, distinguishing unreachability
from every finite barrier depth.
-/

namespace HardProblems

open scoped ENNReal

variable {X : Type*}

/-- An admissible path in the configuration graph `Adj`, from `x` to `y`,
recorded as its list of visited configurations. -/
structure PathBetween (Adj : X → X → Prop) (x y : X) where
  points : List X
  head_eq : points.head? = some x
  last_eq : points.getLast? = some y
  admissible : points.IsChain Adj

/-- A weak local maximum: no single admissible change improves `J`. -/
def IsLocalMax (Adj : X → X → Prop) (J : X → ℝ) (x : X) : Prop :=
  ∀ y, Adj x y → J y ≤ J x

/-- Barrier height from `x` to `y`: the infimum, over admissible paths, of the
deepest dip below `J x` along the path (dips measured in `ℝ≥0∞`, so paths
that never dip contribute `0`). Empty infimum is `⊤`: no path, infinite
barrier. -/
noncomputable def barrier (Adj : X → X → Prop) (J : X → ℝ) (x y : X) : ℝ≥0∞ :=
  ⨅ γ : PathBetween Adj x y, ⨆ z ∈ γ.points, ENNReal.ofReal (J x - J z)

/-- A positive barrier means every admissible route to `y` contains a
configuration strictly worse than the start. No hypothesis here says that `y`
is better than the start or that the dip occurs before first reaching `y`. -/
theorem exists_dip_of_barrier_pos {Adj : X → X → Prop} {J : X → ℝ} {x y : X}
    (h : 0 < barrier Adj J x y) (γ : PathBetween Adj x y) :
    ∃ z ∈ γ.points, J z < J x := by
  have hγ : 0 < ⨆ z ∈ γ.points, ENNReal.ofReal (J x - J z) :=
    lt_of_lt_of_le h (iInf_le _ γ)
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp hγ
  obtain ⟨hmem, hpos⟩ := lt_iSup_iff.mp hz
  refine ⟨z, hmem, ?_⟩
  have := ENNReal.ofReal_pos.mp hpos
  linarith

/-- No admissible path at all makes the barrier infinite. -/
theorem barrier_eq_top_of_no_path {Adj : X → X → Prop} {J : X → ℝ} {x y : X}
    (h : IsEmpty (PathBetween Adj x y)) :
    barrier Adj J x y = ⊤ :=
  iInf_of_empty _

/-- If some admissible path never dips below the start value, the barrier
vanishes: the converse companion to `exists_dip_of_barrier_pos`. (Also
proved independently by Harmonic's Aristotle prover; see `aristotle/`.) -/
theorem barrier_eq_zero_of_monotone_path {Adj : X → X → Prop} {J : X → ℝ}
    {x y : X} (γ : PathBetween Adj x y) (hγ : ∀ z ∈ γ.points, J x ≤ J z) :
    barrier Adj J x y = 0 := by
  refine le_antisymm ?_ zero_le
  refine le_trans (iInf_le _ γ) ?_
  refine iSup_le fun z => iSup_le fun hz => ?_
  simp [ENNReal.ofReal_eq_zero, hγ z hz]

/-! ### Barriers as superlevel reachability

The barrier sits below a positive depth exactly when the target is reachable
through the corresponding strict superlevel region. -/

/-- A supremum of `ENNReal`-valued quantities indexed by membership in a
`List` is strictly below a positive bound as soon as each member is. -/
theorem biSup_list_lt {Y : Type*} (f : Y → ℝ≥0∞) {d : ℝ≥0∞} (hd : 0 < d) :
    ∀ l : List Y, (∀ z ∈ l, f z < d) → (⨆ z ∈ l, f z) < d := by
  intro l
  induction l with
  | nil => intro _; simpa using hd
  | cons a t ih =>
      intro h
      rw [show (⨆ z ∈ (a :: t), f z) = f a ⊔ ⨆ z ∈ t, f z by
        simp [List.mem_cons, iSup_or, iSup_sup_eq]]
      exact sup_lt_iff.2 ⟨h a (by simp), ih fun z hz => h z (by simp [hz])⟩

/-- The barrier sits strictly below `d` exactly when some admissible path
keeps every dip strictly below `d`. The backward direction uses the
finiteness of a path's point list: finitely many quantities each below `d`
have supremum below `d`. -/
theorem barrier_lt_iff {Adj : X → X → Prop} {J : X → ℝ} {x y : X}
    {d : ℝ≥0∞} :
    barrier Adj J x y < d ↔
      ∃ γ : PathBetween Adj x y, ∀ z ∈ γ.points,
        ENNReal.ofReal (J x - J z) < d := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 h
    exact ⟨γ, fun z hz =>
      lt_of_le_of_lt (le_biSup (fun z => ENNReal.ofReal (J x - J z)) hz) hγ⟩
  · rintro ⟨γ, hγ⟩
    have hx : x ∈ γ.points := List.mem_of_mem_head? γ.head_eq
    have hd : 0 < d := lt_of_le_of_lt zero_le (hγ x hx)
    exact lt_of_le_of_lt (iInf_le _ γ) (biSup_list_lt _ hd γ.points hγ)

/-! ### Forward path transport and changed move relations

An edge-preserving map transports concrete paths forward. The separate
two-adjacency witness below changes the move relation and is therefore an
action-set extension, not a coordinate change or abstraction theorem. -/

/-- An edge-preserving state map sends paths to paths. -/
def PathBetween.map {X X' : Type*} {Adj : X → X → Prop}
    {Adj' : X' → X' → Prop} (φ : X → X')
    (hφ : ∀ {a b}, Adj a b → Adj' (φ a) (φ b)) {x y : X}
    (γ : PathBetween Adj x y) : PathBetween Adj' (φ x) (φ y) where
  points := γ.points.map φ
  head_eq := by rw [List.head?_map, γ.head_eq]; rfl
  last_eq := by rw [List.getLast?_map, γ.last_eq]; rfl
  admissible := (List.isChain_map φ).mpr (γ.admissible.imp fun _ _ h => hφ h)

/-- If the mapped endpoints are unreachable in the target graph, no path
between the selected source endpoints could have existed. This is only the
concrete-to-abstract direction. -/
theorem isEmpty_of_map_isEmpty {X X' : Type*} {Adj : X → X → Prop}
    {Adj' : X' → X' → Prop} (φ : X → X')
    (hφ : ∀ {a b}, Adj a b → Adj' (φ a) (φ b)) {x y : X}
    (h : IsEmpty (PathBetween Adj' (φ x) (φ y))) :
    IsEmpty (PathBetween Adj x y) :=
  ⟨fun γ => h.false (γ.map φ hφ)⟩

/-- Changing the move relation can change an infinite barrier to zero even
when the state type, endpoints, and objective remain fixed. The witness replaces
the empty adjacency relation with the universal one. -/
theorem exists_escape_hatch :
    ∃ (Adj Adj' : Bool → Bool → Prop) (J : Bool → ℝ),
      barrier Adj J false true = ⊤ ∧ barrier Adj' J false true = 0 := by
  refine ⟨fun _ _ => False, fun _ _ => True, fun _ => 0, ?_, ?_⟩
  · apply barrier_eq_top_of_no_path
    constructor
    rintro ⟨pts, hh, hl, hc⟩
    match pts, hh, hl, hc with
    | [a], hh, hl, _ =>
      simp only [List.head?_cons, Option.some_inj] at hh
      simp only [List.getLast?_singleton, Option.some_inj] at hl
      rw [hh] at hl
      exact Bool.false_ne_true hl
    | a :: b :: t, _, _, hc =>
      exact (List.isChain_cons.mp hc).1 b (by simp)
  · exact barrier_eq_zero_of_monotone_path
      ⟨[false, true], rfl, rfl, by simp [List.isChain_cons]⟩
      (fun z _ => le_rfl)

/-- Goal reflection: success at the image of a concrete state implies success
at that concrete state. Path lifting is a separate requirement. -/
def Reflects {X X' : Type*} (φ : X → X') (P : X → Prop) (P' : X' → Prop) : Prop :=
  ∀ x, P' (φ x) → P x

/-! ### Zero barrier to a coordinatewise maximizer in the separable model

An additively separable objective on the configuration hypercube has a
nondecreasing flip path from every state to a coordinatewise maximizer. This
does not characterize barriers to other targets or under other move relations. -/

/-- Single-coordinate-flip adjacency on the hypercube. -/
def flipAdj {V : Type*} [DecidableEq V] (p q : V → Bool) : Prop :=
  ∃ v, q = Function.update p v (!(p v))

/-- Helper: if every coordinate on which `p` disagrees with `y` occurs in a
duplicate-free list `l`, there is a flip path from `p` to `y` along which
the separable objective never drops below its value at `p`. -/
theorem exists_monotone_flipPath {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → Bool → ℝ) (y : V → Bool) (hy : ∀ v b, f v b ≤ f v (y v)) :
    ∀ l : List V, l.Nodup → ∀ p : V → Bool, (∀ v, p v ≠ y v → v ∈ l) →
      ∃ γ : PathBetween flipAdj p y,
        ∀ z ∈ γ.points, ∑ w, f w (p w) ≤ ∑ w, f w (z w) := by
  intro l
  induction l with
  | nil =>
      intro _ p hp
      have hpy : p = y := funext fun v => by
        by_contra hv
        simpa using hp v hv
      refine ⟨⟨[p], rfl, by simp [hpy], List.isChain_singleton _⟩, ?_⟩
      intro z hz
      rw [List.mem_singleton] at hz
      subst hz
      exact le_rfl
  | cons v t ih =>
      intro hnd p hp
      have htnd : t.Nodup := (List.nodup_cons.1 hnd).2
      by_cases hv : p v = y v
      · refine ih htnd p fun w hw => ?_
        rcases List.mem_cons.1 (hp w hw) with rfl | hwt
        · exact absurd hv hw
        · exact hwt
      · obtain ⟨p', hp'⟩ : ∃ p', p' = Function.update p v (y v) := ⟨_, rfl⟩
        have hstep : p' = Function.update p v (!(p v)) := by
          have hnot : y v = !(p v) := by
            revert hv; cases p v <;> cases y v <;> simp
          rw [hp', hnot]
        have hmono : ∑ w, f w (p w) ≤ ∑ w, f w (p' w) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rcases eq_or_ne w v with rfl | hw
          · rw [hp', Function.update_self]; exact hy w (p w)
          · rw [hp', Function.update_of_ne hw]
        have hp'mem : ∀ w, p' w ≠ y w → w ∈ t := by
          intro w hw
          rcases eq_or_ne w v with rfl | hne
          · rw [hp', Function.update_self] at hw; exact absurd rfl hw
          · rw [hp', Function.update_of_ne hne] at hw
            rcases List.mem_cons.1 (hp w hw) with rfl | hwt
            · exact absurd rfl hne
            · exact hwt
        obtain ⟨γ', hγ'⟩ := ih htnd p' hp'mem
        refine ⟨⟨p :: γ'.points, rfl, List.mem_getLast?_cons γ'.last_eq, ?_⟩, ?_⟩
        · refine List.isChain_cons.2 ⟨fun q hq => ?_, γ'.admissible⟩
          rw [γ'.head_eq, Option.mem_def, Option.some_inj] at hq
          exact ⟨v, hq ▸ hstep⟩
        · intro z hz
          rcases List.mem_cons.1 hz with rfl | hzt
          · exact le_rfl
          · exact hmono.trans (hγ' z hzt)

/-- An additively separable objective admits a nondecreasing flip path from any
configuration to the coordinatewise maximizer, so that particular barrier
vanishes. -/
theorem barrier_eq_zero_of_separable {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → Bool → ℝ) (x y : V → Bool)
    (hy : ∀ v b, f v b ≤ f v (y v)) :
    barrier flipAdj (fun z => ∑ v, f v (z v)) x y = 0 := by
  obtain ⟨γ, hγ⟩ := exists_monotone_flipPath f y hy (Finset.univ : Finset V).toList
    (Finset.univ.nodup_toList) x fun v _ => Finset.mem_toList.2 (Finset.mem_univ v)
  refine le_antisymm ((iInf_le _ γ).trans ?_) zero_le
  refine iSup_le fun z => iSup_le fun hz => ?_
  refine le_of_eq (ENNReal.ofReal_eq_zero.2 ?_)
  have h := hγ z hz
  simp only [sub_nonpos]
  exact h

/-- On the two-coordinate hypercube there is an objective and a configuration
that no single-coordinate flip improves, while changing both coordinates at
once does improve it. Local maximality therefore depends on the adjacency
relation. -/
theorem exists_unilaterally_stable_not_joint_max :
    ∃ (J : (Fin 2 → Bool) → ℝ) (x : Fin 2 → Bool),
      IsLocalMax flipAdj J x ∧ ¬ IsLocalMax (fun p q => p ≠ q) J x := by
  refine ⟨fun z => if z 0 = true ∧ z 1 = true then 3
      else if z 0 = false ∧ z 1 = false then 2 else 1,
    fun _ => false, ?_, ?_⟩
  · rintro y ⟨v, rfl⟩
    fin_cases v <;> simp [Function.update]
  · intro h
    have h2 := h (fun _ => true) fun hEq => by simpa using congrFun hEq 0
    norm_num at h2

/-- The superlevel reading: for a real depth `d > 0`, the barrier is below
`d` exactly when some admissible path stays inside the superlevel region
`{z | J x - d < J z}`. -/
theorem barrier_lt_iff_superlevel {Adj : X → X → Prop} {J : X → ℝ}
    {x y : X} {d : ℝ} (hd : 0 < d) :
    barrier Adj J x y < ENNReal.ofReal d ↔
      ∃ γ : PathBetween Adj x y, ∀ z ∈ γ.points, J x - d < J z := by
  rw [barrier_lt_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, fun z hz => ?_⟩
    have := (ENNReal.ofReal_lt_ofReal_iff hd).1 (hγ z hz)
    linarith
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, fun z hz => (ENNReal.ofReal_lt_ofReal_iff hd).2 ?_⟩
    have := hγ z hz
    linarith

/-! ### Backed shortcuts: contraction-hierarchy soundness

A shortcut relation `S` over the declared move set `Adj` is *backed* when
every shortcut edge is witnessed by an admissible base path; the strong
form asks that the witness never dip below the lower of the shortcut's two
endpoints. The theorems below show that such shortcuts preserve reachability
and barrier height. The extra depth hypothesis is substantive: mere `Nonempty`
backing does not suffice. On `Fin 3`, take the path `0 → 1 → 2`, values
`J 0 = J 2 = 0` and `J 1 = -1`, and the shortcut `S 0 2`. The union barrier
is `0` while the base barrier is `ENNReal.ofReal 1`. -/

/-- Appending across a shared junction point: if `l₁` ends at `a` and
`a :: l₂` ends at `y`, then `l₁ ++ l₂` ends at `y`. -/
private theorem getLast?_append_of_getLast? {l₁ l₂ : List X} {a y : X}
    (h₁ : l₁.getLast? = some a) (h₂ : (a :: l₂).getLast? = some y) :
    (l₁ ++ l₂).getLast? = some y := by
  match l₂ with
  | [] =>
      simp only [List.getLast?_singleton, Option.some_inj] at h₂
      simpa [h₂] using h₁
  | b :: t =>
      rw [List.getLast?_append_of_ne_nil _ (by simp)]
      rwa [List.getLast?_cons_cons] at h₂

/-- Splice at the level of point lists: a chain over the union relation
starting at `x` and ending at `y` becomes a chain over `Adj` starting at
`x` and ending at `y`, every point of which is `g`-above some point of the
original chain. -/
private theorem splice_chain {Adj S : X → X → Prop} {g : X → ℝ}
    (hback : ∀ u w, S u w → ∃ δ : PathBetween Adj u w,
      ∀ z ∈ δ.points, min (g u) (g w) ≤ g z) :
    ∀ (t : List X) (x y : X), (x :: t).IsChain (fun a b => Adj a b ∨ S a b) →
      (x :: t).getLast? = some y →
      ∃ m : List X, (x :: m).IsChain Adj ∧ (x :: m).getLast? = some y ∧
        ∀ z ∈ x :: m, ∃ p ∈ x :: t, g p ≤ g z := by
  intro t
  induction t with
  | nil =>
      intro x y _ hlast
      simp only [List.getLast?_singleton, Option.some_inj] at hlast
      subst hlast
      exact ⟨[], List.isChain_singleton _, rfl, fun z hz => ⟨z, hz, le_rfl⟩⟩
  | cons a t ih =>
      intro x y hchain hlast
      obtain ⟨hxa, hrest⟩ := List.isChain_cons_cons.1 hchain
      have hlast' : (a :: t).getLast? = some y := by
        rwa [List.getLast?_cons_cons] at hlast
      obtain ⟨m, hmchain, hmlast, hminv⟩ := ih a y hrest hlast'
      rcases hxa with hxa | hxa
      · refine ⟨a :: m, List.isChain_cons_cons.2 ⟨hxa, hmchain⟩,
          List.mem_getLast?_cons hmlast, ?_⟩
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨z, List.mem_cons_self, le_rfl⟩
        · obtain ⟨p, hp, hple⟩ := hminv z hz
          exact ⟨p, List.mem_cons_of_mem _ hp, hple⟩
      · obtain ⟨δ, hδ⟩ := hback x a hxa
        obtain ⟨d, hd⟩ : ∃ d, δ.points = x :: d := by
          match hpts : δ.points, δ.head_eq with
          | b :: d, h =>
              simp only [List.head?_cons, Option.some_inj] at h
              exact ⟨d, by rw [h]⟩
        have hdlast : (x :: d).getLast? = some a := hd ▸ δ.last_eq
        have hdchain : (x :: d).IsChain Adj := hd ▸ δ.admissible
        have hmtail : m.IsChain Adj := (List.isChain_cons.1 hmchain).2
        have hjunction : ∀ q ∈ m.head?, Adj a q := (List.isChain_cons.1 hmchain).1
        refine ⟨d ++ m, ?_, ?_, ?_⟩
        · refine hdchain.append hmtail ?_
          intro p hp q hq
          rw [Option.mem_def, hdlast, Option.some_inj] at hp
          subst hp
          exact hjunction q hq
        · exact getLast?_append_of_getLast? (l₂ := m) hdlast hmlast
        · intro z hz
          have hz' : z ∈ (x :: d) ++ m := hz
          rcases List.mem_append.1 hz' with hz | hz
          · have hmin := hδ z (hd ▸ hz)
            rcases le_total (g x) (g a) with hle | hle
            · rw [min_eq_left hle] at hmin
              exact ⟨x, List.mem_cons_self, hmin⟩
            · rw [min_eq_right hle] at hmin
              exact ⟨a, List.mem_cons_of_mem _ (List.mem_cons_self), hmin⟩
          · obtain ⟨p, hp, hple⟩ := hminv z (List.mem_cons_of_mem _ hz)
            exact ⟨p, List.mem_cons_of_mem _ hp, hple⟩

/-- Splice, packaged for paths: a path over the union relation becomes an
`Adj`-path with the same endpoints, every point of which is `g`-above some
point of the original path. -/
private theorem exists_splice {Adj S : X → X → Prop} {g : X → ℝ}
    (hback : ∀ u w, S u w → ∃ δ : PathBetween Adj u w,
      ∀ z ∈ δ.points, min (g u) (g w) ≤ g z) {x y : X}
    (γ : PathBetween (fun a b => Adj a b ∨ S a b) x y) :
    ∃ γ' : PathBetween Adj x y, ∀ z ∈ γ'.points, ∃ p ∈ γ.points, g p ≤ g z := by
  obtain ⟨pts, hh, hl, hc⟩ := γ
  match pts, hh, hl, hc with
  | b :: t, hh, hl, hc =>
      simp only [List.head?_cons, Option.some_inj] at hh
      subst hh
      obtain ⟨m, hm1, hm2, hm3⟩ := splice_chain hback t b y hc hl
      exact ⟨⟨b :: m, rfl, hm2, hm1⟩, hm3⟩

/-- Any `Adj`-path is a path over the enlarged relation, with the very same
points. -/
def PathBetween.inl {Adj S : X → X → Prop} {x y : X}
    (γ : PathBetween Adj x y) : PathBetween (fun a b => Adj a b ∨ S a b) x y where
  points := γ.points
  head_eq := γ.head_eq
  last_eq := γ.last_eq
  admissible := γ.admissible.imp fun _ _ h => Or.inl h

/-- Reachability form: shortcuts backed by mere admissible paths do not
change what is reachable. -/
theorem pathBetween_shortcut_nonempty_iff {Adj S : X → X → Prop}
    (hback : ∀ u w, S u w → Nonempty (PathBetween Adj u w)) (x y : X) :
    Nonempty (PathBetween (fun a b => Adj a b ∨ S a b) x y) ↔
      Nonempty (PathBetween Adj x y) := by
  constructor
  · rintro ⟨γ⟩
    have hback' : ∀ u w, S u w → ∃ δ : PathBetween Adj u w,
        ∀ z ∈ δ.points, min ((fun _ : X => (0 : ℝ)) u) ((fun _ : X => (0 : ℝ)) w)
          ≤ (fun _ : X => (0 : ℝ)) z := by
      intro u w h
      obtain ⟨δ⟩ := hback u w h
      exact ⟨δ, fun _ _ => by simp⟩
    obtain ⟨γ', -⟩ := exists_splice hback' γ
    exact ⟨γ'⟩
  · rintro ⟨γ⟩
    exact ⟨γ.inl⟩

/-- Sufficient barrier certificate: shortcuts whose witnesses never dip below
the lower of their endpoints leave every barrier height unchanged. The theorem
does not claim that this certificate is necessary. -/
theorem barrier_shortcut_eq {Adj S : X → X → Prop} {J : X → ℝ}
    (hback : ∀ u w, S u w → ∃ γ : PathBetween Adj u w,
      ∀ z ∈ γ.points, min (J u) (J w) ≤ J z) (x y : X) :
    barrier (fun a b => Adj a b ∨ S a b) J x y = barrier Adj J x y := by
  refine le_antisymm (le_iInf fun γ => ?_) (le_iInf fun γ => ?_)
  · exact iInf_le_of_le γ.inl le_rfl
  · obtain ⟨γ', hγ'⟩ := exists_splice hback γ
    refine iInf_le_of_le γ' (iSup_le fun z => iSup_le fun hz => ?_)
    obtain ⟨p, hp, hple⟩ := hγ' z hz
    have key : ENNReal.ofReal (J x - J z) ≤ ENNReal.ofReal (J x - J p) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    exact key.trans (le_biSup (fun p => ENNReal.ofReal (J x - J p)) hp)

/-- The two-step chain `0 → 1 → 2` on `Fin 3`. -/
private def hideAdj (a b : Fin 3) : Prop := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

/-- The single shortcut `0 → 2`. -/
private def hideS (a b : Fin 3) : Prop := a = 0 ∧ b = 2

/-- The valley: `J 0 = J 2 = 0`, `J 1 = -1`. -/
private noncomputable def hideJ : Fin 3 → ℝ := fun a => if a = 1 then -1 else 0

private theorem hideJ_zero : hideJ 0 = 0 := by simp [hideJ]

private theorem hideJ_one : hideJ 1 = -1 := by simp [hideJ]

private theorem hideJ_two : hideJ 2 = 0 := by simp [hideJ]

/-- Every `hideAdj`-path from `0` to `2` visits `1`: its head is `0`, the
singleton path would force `0 = 2`, and the first chain step out of `0`
can only land on `1`. -/
private theorem one_mem_of_path (γ : PathBetween hideAdj 0 2) :
    (1 : Fin 3) ∈ γ.points := by
  obtain ⟨pts, hh, hl, hc⟩ := γ
  match pts, hh, hl, hc with
  | [a], hh, hl, _ =>
      simp only [List.head?_cons, Option.some_inj] at hh
      simp only [List.getLast?_singleton, Option.some_inj] at hl
      rw [hh] at hl
      exact absurd hl (by decide)
  | a :: b :: t, hh, _, hc =>
      simp only [List.head?_cons, Option.some_inj] at hh
      subst hh
      have hstep : ((0 : Fin 3) = 0 ∧ b = 1) ∨ ((0 : Fin 3) = 1 ∧ b = 2) :=
        (List.isChain_cons_cons.mp hc).1
      rcases hstep with ⟨-, rfl⟩ | ⟨h0, -⟩
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd h0 (by decide)

/-- Mere `Nonempty` backing is insufficient for barrier preservation: a
shortcut can hide a valley. On the
two-step chain with a dip in the middle, admitting the backed shortcut
`0 → 2` drops the barrier from `ENNReal.ofReal 1` to `0`. This does not show
that the sufficient depth condition of `barrier_shortcut_eq` is necessary. -/
theorem exists_shortcut_hiding_valley :
    ∃ (Adj S : Fin 3 → Fin 3 → Prop) (J : Fin 3 → ℝ),
      (∀ u w, S u w → Nonempty (PathBetween Adj u w)) ∧
      ∃ x y : Fin 3,
        barrier (fun a b => Adj a b ∨ S a b) J x y < barrier Adj J x y := by
  refine ⟨hideAdj, hideS, hideJ, ?_, 0, 2, ?_⟩
  · intro u w huw
    obtain ⟨rfl, rfl⟩ : u = 0 ∧ w = 2 := huw
    refine ⟨⟨[0, 1, 2], rfl, rfl, ?_⟩⟩
    refine List.isChain_cons_cons.2 ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
    exact List.isChain_cons_cons.2 ⟨Or.inr ⟨rfl, rfl⟩, List.isChain_singleton _⟩
  · have hunion : barrier (fun a b => hideAdj a b ∨ hideS a b) hideJ 0 2 = 0 := by
      refine barrier_eq_zero_of_monotone_path ⟨[0, 2], rfl, rfl, ?_⟩ ?_
      · exact List.isChain_cons_cons.2 ⟨Or.inr ⟨rfl, rfl⟩, List.isChain_singleton _⟩
      · intro z hz
        have hz' : z = 0 ∨ z = 2 := by simpa using hz
        rcases hz' with rfl | rfl
        · exact le_rfl
        · rw [hideJ_zero, hideJ_two]
    have hlow : ENNReal.ofReal 1 ≤ barrier hideAdj hideJ 0 2 := by
      refine le_iInf fun γ => ?_
      have hmem : (1 : Fin 3) ∈ γ.points := one_mem_of_path γ
      have hval : ENNReal.ofReal 1 = ENNReal.ofReal (hideJ 0 - hideJ 1) := by
        rw [hideJ_zero, hideJ_one]; norm_num
      rw [hval]
      exact le_biSup (fun z => ENNReal.ofReal (hideJ 0 - hideJ z)) hmem
    rw [hunion]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr one_pos) hlow

end HardProblems
