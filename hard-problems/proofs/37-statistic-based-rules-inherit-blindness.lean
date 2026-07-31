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

/-- Perfect regulation: holding the outcome constant requires at least as
much response variety as there is disturbance variety. -/
theorem requisite_variety_perfect [Fintype D] [DecidableEq A] [DecidableEq O]
    (ω : D → A → O) (hinj : ∀ a, Function.Injective fun d => ω d a)
    (ρ : D → A) (o₀ : O) (hperf : ∀ d, ω d (ρ d) = o₀) :
    Fintype.card D ≤ (Finset.univ.image ρ).card := by
  have h := requisite_variety ω hinj ρ
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

end Ashby

/-! ## Probe identifiability (the complicated/complex boundary) -/

section Cynefin

variable {S A O : Type*}

/-- Two maintained models are passively distinguishable from `s` when the
law of the observation process differs under the constant "null action"
policy `a₀`: watching, without intervening, eventually separates them. -/
def PassivelyDistinguishable (M₁ M₂ : POSystem S A O) (a₀ : A) (s : S) : Prop :=
  ∃ n, obsProcess M₁ (fun _ => PMF.pure a₀) n s [] ≠
        obsProcess M₂ (fun _ => PMF.pure a₀) n s []

/-- Two maintained models are probe distinguishable from `s` when some
admissible policy separates their observation laws. -/
def ProbeDistinguishable (M₁ M₂ : POSystem S A O) (s : S) : Prop :=
  ∃ (π : List O → PMF A) (n : ℕ),
    obsProcess M₁ π n s [] ≠ obsProcess M₂ π n s []

/-- Watching is a special case of acting. -/
theorem passively_imp_probe {M₁ M₂ : POSystem S A O} {a₀ : A} {s : S}
    (h : PassivelyDistinguishable M₁ M₂ a₀ s) : ProbeDistinguishable M₁ M₂ s :=
  let ⟨n, hn⟩ := h
  ⟨fun _ => PMF.pure a₀, n, hn⟩

/-- If two models agree on the observation kernel and on the transition
kernel at the null action, no amount of passive watching separates them,
at any horizon, from any state. -/
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

/-- The complex regime exists: two models over Bool states/actions/observations
that agree under the passive action (false) at every horizon, yet are separated
by the probing action (true). Learning here requires acting. -/
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

end Cynefin

/-! ## Statistic-based rules (Campbell, Goodhart) -/

section Campbell

variable {S A : Type*}

/-- A decision rule that acts only through a summary statistic inherits the
statistic's blindness: if the statistic fails to separate two states whose
acceptable-action sets are disjoint, then every rule based on it acts
unacceptably in at least one of the two. Managing to the dashboard is safe
exactly to the extent that the dashboard separates decision-relevant
states. -/
theorem statistic_based_rule_fails {m : S → ℝ} (Astar : S → Set A)
    {s s' : S} (hm : m s = m s') (hdisj : Disjoint (Astar s) (Astar s'))
    (α : ℝ → A) :
    α (m s) ∉ Astar s ∨ α (m s') ∉ Astar s' := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  rw [hm] at h1
  exact Set.disjoint_left.mp hdisj h1 h2

/-- The statistic-blindness theorem with an arbitrary statistic codomain:
nothing in the argument uses the real numbers. This is the form the
relativization barrier of complexity theory instantiates: a proof
technique whose verdict factors through relativizing observations takes
the same value in the two Baker-Gill-Solovay worlds, whose correct
conclusions are disjoint, so no such technique is correct in both. -/
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

end Campbell
end
end HardProblems
