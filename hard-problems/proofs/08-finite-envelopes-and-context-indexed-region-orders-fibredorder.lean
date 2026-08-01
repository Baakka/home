import Mathlib

/-!
This snippet is about:

  SplitIndexedOrder
  reindexHom
  reindex_id_apply
  reindex_comp_apply
  performanceRegions
  CompatibleEncounterRegions
  RealizedRegion
  instPartialOrderRealizedRegion
  reindexRealized
  reindexRealized_val
  realizedRegionOrder
  realizedRegionOrder_reindex_val
  ambient_preimage_can_be_unrealized
  EncounterLE
  encounterLE_refl
  encounterLE_trans
  encounterLE_antisymmetric_iff_injective
  constant_region_not_antisymmetric
  surjective_preimage_subset_iff
  equiv_preimage_subset_iff
  equiv_preimage_preserves_inclusion
  equiv_preimage_reflects_inclusion
  nonsurjective_preimage_not_order_reflecting
  noninjective_image_not_order_reflecting

found at line 353 of 375, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/FibredOrder.lean -/


/-!
# The fibred order of difficulty

This module formalizes a small, strict version of a context-indexed order.
Each object of a category of comparison contexts carries a partial order, and
each context morphism acts contravariantly by a monotone reindexing map. The
identity and composition laws hold as specified pointwise equalities.

For performance comparison, a context `c` has a type `Perf.obj c` of
performance points and a fiber `Set (Perf.obj c)` of candidate regions.
Lean's order on this fiber is set inclusion. Thus `A ≤ B` literally means
that `A` contains no point outside `B`. When `A` and `B` are realized
attainable regions in one comparison context, the book reads this as "`A` is
at least as hard as `B`". A context map translates performance points
covariantly, while regions reindex contravariantly by preimage.

The ambient construction contains every candidate subset of the performance
type. A second construction restricts to subsets realized by admitted
encounters when compatible encounter transport is supplied. Without that
extra semantics, preimage need not preserve realizability.

This is an indexed-poset presentation with a chosen splitting. It does not
construct the Grothendieck total category, prove a cartesian lifting universal
property, or identify unrelated fibers without a supplied context morphism.
-/

namespace HardProblems
namespace FibredOrder

open CategoryTheory

universe v u w

/-- A strict contravariant family of partial orders over a category.

The pointwise identity and composition equations record a chosen splitting.
They are the only categorical coherence claimed in this file. -/
structure SplitIndexedOrder (C : Type u) [Category.{v} C] where
  /-- The carrier of the ordered fiber over a context. -/
  Fiber : C → Type w
  /-- The partial order in each fiber. -/
  fiberOrder : (c : C) → PartialOrder (Fiber c)
  /-- Contravariant transport along a context morphism. -/
  reindex : {c d : C} → (c ⟶ d) → Fiber d → Fiber c
  /-- Reindexing along an identity is the identity. -/
  reindex_id : ∀ (c : C) (x : Fiber c), reindex (𝟙 c) x = x
  /-- Reindexing reverses categorical composition. -/
  reindex_comp : ∀ {c d e : C} (f : c ⟶ d) (g : d ⟶ e)
    (x : Fiber e), reindex (f ≫ g) x = reindex f (reindex g x)
  /-- Every reindexing map is monotone in the fiber orders. -/
  reindex_mono : ∀ {c d : C} (f : c ⟶ d) {x y : Fiber d},
    (fiberOrder d).le x y → (fiberOrder c).le (reindex f x) (reindex f y)

namespace SplitIndexedOrder

variable {C : Type u} [Category.{v} C]

/-- Install the declared order when working in one fiber. -/
instance instPartialOrder (P : SplitIndexedOrder C) (c : C) :
    PartialOrder (P.Fiber c) :=
  P.fiberOrder c

/-- Reindexing as an order homomorphism. -/
def reindexHom (P : SplitIndexedOrder C) {c d : C} (f : c ⟶ d) :
    P.Fiber d →o P.Fiber c where
  toFun := P.reindex f
  monotone' := by
    intro x y hxy
    exact P.reindex_mono f hxy

@[simp]
theorem reindex_id_apply (P : SplitIndexedOrder C) (c : C) (x : P.Fiber c) :
    P.reindex (𝟙 c) x = x :=
  P.reindex_id c x

@[simp]
theorem reindex_comp_apply (P : SplitIndexedOrder C) {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) (x : P.Fiber e) :
    P.reindex (f ≫ g) x = P.reindex f (P.reindex g x) :=
  P.reindex_comp f g x

end SplitIndexedOrder

/-! ## Ambient performance regions -/

/-- The context-indexed partial order of all candidate performance regions
induced by a functor of performance-coordinate types. Context morphisms act
on points by `Perf.map`; candidate regions move in the opposite direction by
preimage. Realizability by an encounter or program is not part of this data. -/
def performanceRegions {C : Type u} [Category.{v} C] (Perf : C ⥤ Type w) :
    SplitIndexedOrder C where
  Fiber c := Set (Perf.obj c)
  fiberOrder _ := inferInstance
  reindex f A := Perf.map f ⁻¹' A
  reindex_id c A := by
    ext x
    simp
  reindex_comp f g A := by
    ext x
    simp
  reindex_mono := by
    intro c d f A B hAB
    exact Set.preimage_mono hAB

/-! ## Conditionally realized regions -/

universe e

/-- Encounter data sufficient to make realized performance regions stable
under contravariant context change.

No identity or composition equation is imposed on `transport` at the level of
raw encounters. Only its observable effect on regions is stored. That exact
compatibility is enough to induce split reindexing after duplicate encounter
witnesses have been forgotten. -/
structure CompatibleEncounterRegions {C : Type u} [Category.{v} C]
    (Perf : C ⥤ Type w) where
  /-- The type of admitted encounters in each context. -/
  Encounter : C → Type e
  /-- The candidate region actually realized by an encounter. -/
  region : (c : C) → Encounter c → Set (Perf.obj c)
  /-- Contravariant transport of encounters along a context map. -/
  transport : {c d : C} → (c ⟶ d) → Encounter d → Encounter c
  /-- Transport realizes exactly the preimage of the target encounter's
  region. -/
  region_transport : ∀ {c d : C} (f : c ⟶ d) (E : Encounter d),
    region c (transport f E) = Perf.map f ⁻¹' region d E

namespace CompatibleEncounterRegions

variable {C : Type u} [Category.{v} C] {Perf : C ⥤ Type w}

/-- A region together with the proposition that some admitted encounter
realizes it. Different encounter witnesses with the same region determine the
same element of this subtype. -/
def RealizedRegion (D : CompatibleEncounterRegions Perf) (c : C) :=
  {A : Set (Perf.obj c) // ∃ E : D.Encounter c, D.region c E = A}

/-- Realized regions inherit the antisymmetric subset order from their
underlying sets; encounter witnesses do not participate in equality. -/
instance instPartialOrderRealizedRegion (D : CompatibleEncounterRegions Perf)
    (c : C) : PartialOrder (D.RealizedRegion c) :=
  PartialOrder.lift Subtype.val Subtype.val_injective

/-- Reindex a realized region by preimage. Compatibility supplies a transported
encounter witnessing that the resulting region is realized in the source
context. -/
def reindexRealized (D : CompatibleEncounterRegions Perf) {c d : C}
    (f : c ⟶ d) (A : D.RealizedRegion d) : D.RealizedRegion c :=
  ⟨Perf.map f ⁻¹' A.1, by
    rcases A.2 with ⟨E, hE⟩
    refine ⟨D.transport f E, ?_⟩
    rw [D.region_transport, hE]⟩

/-- The underlying set of a reindexed realized region is transparently the
ambient preimage. -/
@[simp]
theorem reindexRealized_val (D : CompatibleEncounterRegions Perf) {c d : C}
    (f : c ⟶ d) (A : D.RealizedRegion d) :
    (D.reindexRealized f A).1 = Perf.map f ⁻¹' A.1 :=
  rfl

/-- Realized regions form a split context-indexed partial order. The split laws
hold for region values; they do not assert coherent identity or composition
laws for the chosen raw encounter transports. -/
def realizedRegionOrder (D : CompatibleEncounterRegions Perf) :
    SplitIndexedOrder C where
  Fiber c := D.RealizedRegion c
  fiberOrder _ := inferInstance
  reindex := D.reindexRealized
  reindex_id c A := by
    apply Subtype.ext
    ext x
    simp [reindexRealized]
  reindex_comp f g A := by
    apply Subtype.ext
    ext x
    simp [reindexRealized]
  reindex_mono := by
    intro c d f A B hAB
    exact Set.preimage_mono hAB

/-- The reindexing stored in `realizedRegionOrder` has the same transparent
preimage value as `reindexRealized`. -/
@[simp]
theorem realizedRegionOrder_reindex_val
    (D : CompatibleEncounterRegions Perf) {c d : C}
    (f : c ⟶ d) (A : D.RealizedRegion d) :
    ((D.realizedRegionOrder).reindex f A).1 = Perf.map f ⁻¹' A.1 :=
  rfl

end CompatibleEncounterRegions

/-- Without compatible encounter transport, an ambient preimage need not be
among the regions declared realized in the source context. Both declared
families below are nonempty, yet the preimage of the realized target region is
not a realized source region. -/
theorem ambient_preimage_can_be_unrealized :
    let f : Unit → Bool := fun _ ↦ false
    let sourceRealized : Set (Set Unit) := {∅}
    let targetRegion : Set Bool := {false}
    let targetRealized : Set (Set Bool) := {targetRegion}
    sourceRealized.Nonempty ∧ targetRealized.Nonempty ∧
      targetRegion ∈ targetRealized ∧
      f ⁻¹' targetRegion ∉ sourceRealized := by
  simp

/-! ## Regions versus encounters -/

/-- Compare encounters by inclusion of their attainable regions. This is the
pullback of the fiber order along an encounter-to-region map. -/
def EncounterLE {E : Type u} {P : Type w} (region : E → Set P)
    (x y : E) : Prop :=
  region x ⊆ region y

/-- Region comparison pulled back to encounters is reflexive. -/
theorem encounterLE_refl {E : Type u} {P : Type w} (region : E → Set P)
    (x : E) : EncounterLE region x x :=
  Set.Subset.rfl

/-- Region comparison pulled back to encounters is transitive. -/
theorem encounterLE_trans {E : Type u} {P : Type w} (region : E → Set P)
    {x y z : E} (hxy : EncounterLE region x y)
    (hyz : EncounterLE region y z) : EncounterLE region x z :=
  hxy.trans hyz

/-- The pulled-back comparison is antisymmetric exactly when the
encounter-to-region map is injective. Without injectivity it is only a
preorder on encounters; quotienting encounters by equal regions restores a
partial order. -/
theorem encounterLE_antisymmetric_iff_injective {E : Type u} {P : Type w}
    (region : E → Set P) :
    (∀ ⦃x y : E⦄, EncounterLE region x y →
      EncounterLE region y x → x = y) ↔ Function.Injective region := by
  constructor
  · intro h x y hxy
    apply h
    · simp [EncounterLE, hxy]
    · simp [EncounterLE, hxy]
  · intro hinj x y hxy hyx
    exact hinj (Set.Subset.antisymm hxy hyx)

/-- Two distinct encounters assigned the same region witness the failure of
antisymmetry. The failure is in the encounter presentation, not in the subset
order on regions. -/
theorem constant_region_not_antisymmetric :
    let region : Bool → Set Unit := fun _ ↦ ∅
    EncounterLE region false true ∧ EncounterLE region true false ∧
      false ≠ true := by
  simp [EncounterLE]

/-- Preimage along a surjective point map preserves and reflects inclusion.
Bijectivity is therefore sufficient but not necessary for exact comparison
transport at the level of arbitrary candidate regions. -/
theorem surjective_preimage_subset_iff {X : Type u} {Y : Type w}
    (f : X → Y) (hf : Function.Surjective f) (A B : Set Y) :
    f ⁻¹' A ⊆ f ⁻¹' B ↔ A ⊆ B := by
  constructor
  · intro h y hy
    rcases hf y with ⟨x, rfl⟩
    exact h hy
  · exact Set.preimage_mono

/-- A bijective coordinate change preserves and reflects inclusion after
contravariant reindexing. Hence an exact relabeling neither creates nor erases
comparisons between candidate performance regions. -/
theorem equiv_preimage_subset_iff {X : Type u} {Y : Type w}
    (e : X ≃ Y) (A B : Set Y) :
    e ⁻¹' A ⊆ e ⁻¹' B ↔ A ⊆ B :=
  surjective_preimage_subset_iff e e.surjective A B

/-- The preservation direction of exact coordinate invariance. -/
theorem equiv_preimage_preserves_inclusion {X : Type u} {Y : Type w}
    (e : X ≃ Y) {A B : Set Y} (h : A ⊆ B) :
    e ⁻¹' A ⊆ e ⁻¹' B :=
  (equiv_preimage_subset_iff e A B).2 h

/-- The reflection direction of exact coordinate invariance. It depends on
surjectivity and is unavailable for a general non-surjective coordinate map. -/
theorem equiv_preimage_reflects_inclusion {X : Type u} {Y : Type w}
    (e : X ≃ Y) {A B : Set Y} (h : e ⁻¹' A ⊆ e ⁻¹' B) :
    A ⊆ B :=
  (equiv_preimage_subset_iff e A B).1 h

/-- Explicit failure of preimage order reflection for a non-surjective point
map. The injective constant map `Unit → Bool` misses `true`, so the whole Bool
region and `{false}` have equal preimages even though the former is not
contained in the latter. The issue here is failure of surjectivity, not
many-to-one collapse. -/
theorem nonsurjective_preimage_not_order_reflecting :
    let f : Unit → Bool := fun _ ↦ false
    let A : Set Bool := Set.univ
    let B : Set Bool := {false}
    ¬ Function.Surjective f ∧
      f ⁻¹' A = f ⁻¹' B ∧ f ⁻¹' A ⊆ f ⁻¹' B ∧ ¬ A ⊆ B := by
  dsimp
  constructor
  · intro hf
    rcases hf true with ⟨x, hx⟩
    simp at hx
  constructor
  · ext x
    simp
  constructor
  · intro x hx
    simp
  · intro h
    have : true ∈ ({false} : Set Bool) := h (Set.mem_univ true)
    simp at this

/-- Explicit failure of direct-image order reflection for a noninjective point
map. The constant map `Bool → Unit` merges `false` and `true`, so their
singleton regions have equal direct images although neither singleton is
contained in the other. This is the separate many-to-one failure mode. -/
theorem noninjective_image_not_order_reflecting :
    let f : Bool → Unit := fun _ ↦ ()
    let A : Set Bool := {false}
    let B : Set Bool := {true}
    ¬ Function.Injective f ∧
      f '' A = f '' B ∧ f '' A ⊆ f '' B ∧ ¬ A ⊆ B := by
  dsimp
  constructor
  · intro hf
    have h : false = true := hf rfl
    simp at h
  constructor
  · ext x
    simp
  constructor
  · intro x hx
    simp
  · intro h
    have : false ∈ ({true} : Set Bool) := h (by simp)
    simp at this

end FibredOrder
end HardProblems
