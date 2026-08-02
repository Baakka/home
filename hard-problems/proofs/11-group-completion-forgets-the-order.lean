import Mathlib

/-!
This snippet is about:

  RegionMonoid
  grothendieckGroup_subsingleton_of_idempotent
  grothendieckGroup_regionMonoid_subsingleton
  grothendieckGroup_of_eq_iff
  toGrothendieckGroup_injective_of_cancel
  concrete_regions_collapse
  withTop_cost_top_add_image
  saturating_costs_grothendieckAddGroup_subsingleton

found at line 155 of 181, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/KTheoryCollapse.lean -/


/-!
# The K-theoretic collapse of the difficulty order

Aristotle-verified, ported from mathlib v4.28. The natural decategorification
of the fibred order is group completion: pass from the commutative monoid of
difficulty classes to its Grothendieck group. These results say that the
passage forgets everything the order carried.

* Attainable regions compose by union, union is idempotent, and the
  Grothendieck group of any commutative idempotent monoid is trivial
  (`grothendieckGroup_subsingleton_of_idempotent`); in particular the region
  monoid over every performance space has trivial K-group, with no
  finiteness or nonemptiness assumption doing hidden work.
* The canonical map identifies two classes exactly when some common factor
  multiplies both into agreement (`grothendieckGroup_of_eq_iff`); the factors
  that identify anything new are the non-cancellable ones, and completion is
  injective on the cancellative part (`toGrothendieckGroup_injective_of_cancel`),
  which is where exact resource counts live and the book's subject does not.
* Concretely, the distinct regions `{true}` and `{false}` collapse to the
  same element (`concrete_regions_collapse`), and the saturating cost scale
  `WithTop ℕ` has trivial additive Grothendieck group, so every cost above
  the cap and below it alike is annihilated.

That is why the book works with the order and not its K-group: a group-valued
invariant obtained by completion cannot distinguish any two difficulty
classes at all.
-/

universe u

namespace HardProblems
namespace KTheoryCollapse

open Localization
open Algebra

/-- Attainable-performance regions over a performance space `P`, composing by
union. -/
abbrev RegionMonoid (P : Type u) := Set P

instance (P : Type u) : CommMonoid (RegionMonoid P) where
  mul A B := A ∪ B
  mul_assoc := Set.union_assoc
  one := (∅ : Set P)
  one_mul := Set.empty_union
  mul_one := Set.union_empty
  mul_comm := Set.union_comm

/-- Goal 1': the Grothendieck group of every commutative idempotent monoid is
trivial. -/
theorem grothendieckGroup_subsingleton_of_idempotent
    (M : Type u) [CommMonoid M] (hidem : ∀ a : M, a * a = a) :
    Subsingleton (GrothendieckGroup M) := by
  refine ⟨fun x y => ?_⟩
  -- We'll show all elements equal GrothendieckGroup.of 1
  suffices ∀ z : GrothendieckGroup M, z = GrothendieckGroup.of 1 by rw [this x, this y]
  intro z
  -- Use Quot.induction_on to work with representatives
  induction z using Quot.induction_on with
  | h p => 
    -- p : M × ⊤, need to show Quot.mk oreEqv p = 1
    let ⟨a, b⟩ := p
    -- Need to show Quot.mk oreEqv (a, b) = GrothendieckGroup.of 1
    -- First show GrothendieckGroup.of 1 = Quot.mk oreEqv (1, 1)
    have of_one_eq : GrothendieckGroup.of 1 = Quot.mk (OreLocalization.oreEqv ⊤ M) (1, 1) := by
      rfl
    rw [of_one_eq]
    -- Now use Quot.eq
    apply Quot.sound
    unfold OreLocalization.oreEqv
    -- Need ∃ u v, u • (1,1).1 = v • (a,b).1 ∧ u * (1,1).2 = v * (a,b).2
    -- i.e., ∃ u v, u = v * a ∧ u = v * b
    -- Take v = a * b, u = a * b
    refine ⟨⟨a * b, ?_⟩, a * b, ?_⟩
    · simp
    · constructor
      · -- ⟨a * ↑b, _⟩ • 1 = (a * ↑b) • a
        simp only [Submonoid.mk_smul, smul_eq_mul]
        rw [mul_one]
        conv_rhs => rw [mul_assoc, mul_comm, mul_assoc, hidem]
        rw [mul_comm]
      · -- ↑⟨a * ↑b, _⟩ * ↑(1,1).2 = a * ↑b * ↑(a,b).2
        simp [mul_one]
        rw [mul_assoc, hidem]

/-- Goal 1: the Grothendieck group of the region monoid is trivial, for every
performance type `P` (including the empty type). -/
theorem grothendieckGroup_regionMonoid_subsingleton (P : Type u) :
    Subsingleton (GrothendieckGroup (RegionMonoid P)) := by
  apply grothendieckGroup_subsingleton_of_idempotent
  exact Set.union_self

/-- Goal 2: canonical images are equal exactly when the two elements become
equal after multiplying by a common slack element. -/
theorem grothendieckGroup_of_eq_iff (M : Type u) [CommMonoid M] (a b : M) :
    GrothendieckGroup.of a = GrothendieckGroup.of b ↔
      ∃ c : M, a * c = b * c := by
  change Localization.mk a 1 = Localization.mk b 1 ↔ _
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  simp only [Submonoid.coe_one, one_mul]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by simpa [mul_comm] using hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, Submonoid.mem_top c⟩, by simpa [mul_comm] using hc⟩

/-- Goal 3: for a cancellative cost monoid, the canonical map is injective. -/
theorem toGrothendieckGroup_injective_of_cancel
    (M : Type u) [CancelCommMonoid M] :
    Function.Injective (GrothendieckGroup.of : M → GrothendieckGroup M) := by
  exact GrothendieckGroup.of_injective

/-- Goal 4: the concrete regions `{true}` and `{false}` are distinct but have
the same image in the Grothendieck group. -/
theorem concrete_regions_collapse :
    ({true} : RegionMonoid Bool) ≠ {false} ∧
      GrothendieckGroup.of ({true} : RegionMonoid Bool) =
        GrothendieckGroup.of ({false} : RegionMonoid Bool) := by
  haveI : Subsingleton (GrothendieckGroup (RegionMonoid Bool)) :=
    grothendieckGroup_regionMonoid_subsingleton Bool
  refine ⟨?_, Subsingleton.elim _ _⟩
  simp [Set.eq_singleton_iff_unique_mem]

/-- Goal 5a: adding any cost to the absorbing overflow value does not change
its canonical image. -/
theorem withTop_cost_top_add_image (a : WithTop ℕ) :
    GrothendieckAddGroup.of (⊤ + a) =
      GrothendieckAddGroup.of (⊤ : WithTop ℕ) := by
  simp

/-- Goal 5: because `⊤` is absorbing, the entire Grothendieck group of
`WithTop ℕ` is trivial, not merely the part at or above the cap. -/
theorem saturating_costs_grothendieckAddGroup_subsingleton :
    Subsingleton (GrothendieckAddGroup (WithTop ℕ)) := by
  have hof : ∀ a : WithTop ℕ, GrothendieckAddGroup.of a = 0 := by
    intro a
    apply add_right_cancel (b := GrothendieckAddGroup.of (⊤ : WithTop ℕ))
    rw [← map_add]
    simp
  constructor
  intro x y
  suffices ∀ z : GrothendieckAddGroup (WithTop ℕ), z = 0 by rw [this x, this y]
  intro z
  induction z using AddLocalization.induction_on with
  | _ p =>
    have h : AddLocalization.mk p.1 p.2 +
        GrothendieckAddGroup.of (p.2 : WithTop ℕ) =
        GrothendieckAddGroup.of p.1 := by
      change AddLocalization.mk p.1 p.2 +
          AddLocalization.mk (p.2 : WithTop ℕ) 0 = AddLocalization.mk p.1 0
      rw [AddLocalization.mk_add, AddLocalization.mk_eq_mk_iff,
        AddLocalization.r_iff_exists]
      use 0
      simp [add_comm]
    rw [hof _, hof _] at h
    simpa using h

end KTheoryCollapse
end HardProblems
