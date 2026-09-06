import Mathlib

/-!
This snippet is about:

  GradedComplex
  Cochain
  pair
  coboundary
  stokes
  surface_stokes_of_hodge_curl
  coboundary_coboundary
  IsCycle
  IsBoundary
  Homologous
  isCycle_of_isBoundary
  pair_coboundary_eq_zero_of_isCycle
  ChainMap
  pullback
  coboundary_natural
  map_isCycle
  map_isBoundary
  map_homologous
  boundaryDefect
  boundaryDefect_apply
  boundaryDefect_eq_zero_iff
  boundaryDefect_eq_zero
  boundary_image_eq_neg_defect_of_isCycle
  pair_boundaryDefect
  gradedPullback
  pairingDefect
  pairingDefect_gradedPullback_eq_zero
  coboundaryTransportDefect
  pair_coboundaryTransportDefect_gradedPullback
  taskDefect
  taskDefect_eq_neg_pairingDefect_add
  integerZeroComplex
  integerIdentityMap
  integerZeroObservationMap
  integerOneChain
  boundary_exact_but_pairing_defective
  pairing_exact_but_task_defective
  CellularComplex
  toGradedComplex
  incidence
  boundary_incidence_eq_zero

found at line 414 of 418, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/HigherStokes.lean -/


/-!
# Higher-dimensional boundary accounting

This module isolates the algebraic core needed for Stokes laws in every
degree.  A graded chain complex supplies coefficient modules and boundary
maps whose consecutive composites vanish.  Cochains are the linear duals of
chains, coboundary is precomposition with boundary, and the all-degree Stokes
identity is therefore an exact adjointness statement.

The chain groups may be free constant-coefficient cellular chains, or they may
already contain local coefficient data assembled from cosheaf stalks.  The
dual construction gives the corresponding cochain observations.  This file
does not construct a site or prove sheaf gluing for arbitrary local behavior
assignments.
-/

namespace HardProblems
namespace HigherStokes

universe u v

/-- A nonnegatively graded chain complex, indexed so that `boundary k` maps
degree `k + 1` to degree `k`. -/
structure GradedComplex (R : Type v) [CommRing R] where
  Chain : ℕ → Type u
  [chainAddCommGroup : ∀ k, AddCommGroup (Chain k)]
  [chainModule : ∀ k, Module R (Chain k)]
  boundary : ∀ k, Chain (k + 1) →ₗ[R] Chain k
  boundary_boundary : ∀ k (c : Chain (k + 2)),
    boundary k (boundary (k + 1) c) = 0

attribute [instance] GradedComplex.chainAddCommGroup GradedComplex.chainModule

variable {R : Type v} [CommRing R]

/-- Degree-`k` cochains are linear observations on degree-`k` chains. -/
abbrev Cochain (K : GradedComplex R) (k : ℕ) := K.Chain k →ₗ[R] R

/-- Evaluation pairing between a cochain and a chain. -/
def pair (K : GradedComplex R) {k : ℕ} (φ : Cochain K k) (c : K.Chain k) : R :=
  φ c

/-- Coboundary is dual to boundary. -/
def coboundary (K : GradedComplex R) (k : ℕ) (φ : Cochain K k) :
    Cochain K (k + 1) :=
  φ.comp (K.boundary k)

/-- Higher-dimensional Stokes: accumulated coboundary on a chain equals the
original observation evaluated on the chain's exposed boundary. -/
theorem stokes (K : GradedComplex R) (k : ℕ) (φ : Cochain K k)
    (c : K.Chain (k + 1)) :
    pair K (coboundary K k φ) c = pair K φ (K.boundary k c) := by
  rfl

/-- Conditional circulation--flux form of Stokes.  In a geometric model one
may take `ωF` to be the one-form dual to a vector field and `starCurl` to be
the two-form obtained by applying the Hodge star to the one-form dual to its
curl.  Once the geometric identity `starCurl = coboundary K 1 ωF` is supplied,
the flux through a two-chain equals circulation around its boundary.

This theorem deliberately does not construct a metric, a Hodge star, or a
smooth curl operator. -/
theorem surface_stokes_of_hodge_curl (K : GradedComplex R)
    (ωF : Cochain K 1) (starCurl : Cochain K 2)
    (hcurl : starCurl = coboundary K 1 ωF) (surface : K.Chain 2) :
    pair K ωF (K.boundary 1 surface) = pair K starCurl surface := by
  rw [hcurl, stokes]

/-- The dual differential squares to zero because boundary squares to zero. -/
theorem coboundary_coboundary (K : GradedComplex R) (k : ℕ)
    (φ : Cochain K k) :
    coboundary K (k + 1) (coboundary K k φ) = 0 := by
  ext c
  change φ (K.boundary k (K.boundary (k + 1) c)) = 0
  rw [K.boundary_boundary]
  exact map_zero φ

/-- A positive-degree cycle is a chain with no exposed boundary. -/
def IsCycle (K : GradedComplex R) (k : ℕ) (c : K.Chain (k + 1)) : Prop :=
  K.boundary k c = 0

/-- A positive-degree boundary is the boundary of a chain one degree higher. -/
def IsBoundary (K : GradedComplex R) (k : ℕ) (c : K.Chain (k + 1)) : Prop :=
  ∃ b : K.Chain (k + 2), K.boundary (k + 1) b = c

/-- Two positive-degree chains are homologous when their difference is an
exposed boundary one degree higher. -/
def Homologous (K : GradedComplex R) (k : ℕ)
    (c d : K.Chain (k + 1)) : Prop :=
  ∃ b : K.Chain (k + 2), K.boundary (k + 1) b = c - d

/-- Every boundary is a cycle: the boundary of a boundary vanishes. -/
theorem isCycle_of_isBoundary (K : GradedComplex R) (k : ℕ)
    {c : K.Chain (k + 1)} (hc : IsBoundary K k c) : IsCycle K k c := by
  rcases hc with ⟨b, rfl⟩
  exact K.boundary_boundary k b

/-- Exact cochains vanish on cycles. -/
theorem pair_coboundary_eq_zero_of_isCycle (K : GradedComplex R) (k : ℕ)
    (φ : Cochain K k) {c : K.Chain (k + 1)} (hc : IsCycle K k c) :
    pair K (coboundary K k φ) c = 0 := by
  rw [stokes, hc]
  exact map_zero φ

/-- A degree-preserving coarse-graining is exact for boundary accounting when
it is a chain map.  Its components may identify or linearly aggregate cells. -/
structure ChainMap (K L : GradedComplex R) where
  map : ∀ k, K.Chain k →ₗ[R] L.Chain k
  commutes : ∀ k (c : K.Chain (k + 1)),
    map k (K.boundary k c) = L.boundary k (map (k + 1) c)

/-- Pull a coarse cochain back to the fine complex. -/
def pullback {K L : GradedComplex R} (F : ChainMap K L) (k : ℕ)
    (φ : Cochain L k) : Cochain K k :=
  φ.comp (F.map k)

/-- Pullback along a chain map commutes with coboundary in every degree. -/
theorem coboundary_natural {K L : GradedComplex R} (F : ChainMap K L)
    (k : ℕ) (φ : Cochain L k) :
    coboundary K k (pullback F k φ) =
      pullback F (k + 1) (coboundary L k φ) := by
  ext c
  change φ (F.map k (K.boundary k c)) =
    φ (L.boundary k (F.map (k + 1) c))
  rw [F.commutes]

/-- Exact coarse-graining sends cycles to cycles. -/
theorem ChainMap.map_isCycle {K L : GradedComplex R} (F : ChainMap K L)
    (k : ℕ) {c : K.Chain (k + 1)} (hc : IsCycle K k c) :
    IsCycle L k (F.map (k + 1) c) := by
  unfold IsCycle at hc ⊢
  rw [← F.commutes, hc]
  exact map_zero (F.map k)

/-- Exact coarse-graining sends boundaries to boundaries. -/
theorem ChainMap.map_isBoundary {K L : GradedComplex R} (F : ChainMap K L)
    (k : ℕ) {c : K.Chain (k + 1)} (hc : IsBoundary K k c) :
    IsBoundary L k (F.map (k + 1) c) := by
  rcases hc with ⟨b, rfl⟩
  exact ⟨F.map (k + 2) b, (F.commutes (k + 1) b).symm⟩

/-- Chain maps respect the boundary equivalence used to form homology. -/
theorem ChainMap.map_homologous {K L : GradedComplex R} (F : ChainMap K L)
    (k : ℕ) {c d : K.Chain (k + 1)} (hcd : Homologous K k c d) :
    Homologous L k (F.map (k + 1) c) (F.map (k + 1) d) := by
  rcases hcd with ⟨b, hb⟩
  refine ⟨F.map (k + 2) b, ?_⟩
  rw [← F.commutes, hb, map_sub]

/-- The degree-`k` boundary defect of an arbitrary graded linear
coarse-graining.  It is zero exactly when the boundary square commutes in that
degree. -/
def boundaryDefect {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k) (k : ℕ) :
    K.Chain (k + 1) →ₗ[R] L.Chain k :=
  (q k).comp (K.boundary k) - (L.boundary k).comp (q (k + 1))

theorem boundaryDefect_apply {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k) (k : ℕ)
    (c : K.Chain (k + 1)) :
    boundaryDefect q k c =
      q k (K.boundary k c) - L.boundary k (q (k + 1) c) := by
  rfl

/-- Vanishing defect is exactly the chain-map equation in one degree. -/
theorem boundaryDefect_eq_zero_iff {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k) (k : ℕ) :
    boundaryDefect q k = 0 ↔
      ∀ c : K.Chain (k + 1),
        q k (K.boundary k c) = L.boundary k (q (k + 1) c) := by
  constructor
  · intro h c
    have hc := LinearMap.congr_fun h c
    simpa [boundaryDefect, sub_eq_zero] using hc
  · intro h
    ext c
    simpa [boundaryDefect, sub_eq_zero] using h c

/-- A chain map has zero boundary defect in every degree. -/
theorem ChainMap.boundaryDefect_eq_zero {K L : GradedComplex R}
    (F : ChainMap K L) (k : ℕ) :
    boundaryDefect F.map k = 0 := by
  exact (boundaryDefect_eq_zero_iff F.map k).2 (F.commutes k)

/-- On a fine cycle, the defect is exactly the negative boundary charge that
appears after coarse-graining. -/
theorem boundary_image_eq_neg_defect_of_isCycle {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k) (k : ℕ)
    {c : K.Chain (k + 1)} (hc : IsCycle K k c) :
    L.boundary k (q (k + 1) c) = -boundaryDefect q k c := by
  rw [boundaryDefect_apply, hc, map_zero]
  simp

/-- Pairing an observable with the boundary defect gives exactly the mismatch
between fine-then-coarse and coarse-then-boundary accounting. -/
theorem pair_boundaryDefect {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k) (k : ℕ)
    (φ : Cochain L k) (c : K.Chain (k + 1)) :
    pair L φ (q k (K.boundary k c)) -
        pair K ((coboundary L k φ).comp (q (k + 1))) c =
      pair L φ (boundaryDefect q k c) := by
  change φ (q k (K.boundary k c)) -
      φ (L.boundary k (q (k + 1) c)) =
    φ (q k (K.boundary k c) - L.boundary k (q (k + 1) c))
  exact (map_sub φ _ _).symm

/-- The canonical transport of observations along an arbitrary graded chain
map.  This operation is available even when `q` has a nonzero boundary defect:
it is just precomposition degree by degree. -/
def gradedPullback {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k) :
    ∀ k, Cochain L k →ₗ[R] Cochain K k :=
  fun k =>
    { toFun := fun φ => φ.comp (q k)
      map_add' := by
        intro φ ψ
        ext c
        rfl
      map_smul' := by
        intro r φ
        ext c
        rfl }

/-- Failure of a declared observation transport to be dual to the declared
chain aggregation.  It is intentionally separate from `boundaryDefect`. -/
def pairingDefect {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k)
    (qObs : ∀ k, Cochain L k →ₗ[R] Cochain K k)
    (k : ℕ) (φ : Cochain L k) (c : K.Chain k) : R :=
  pair K (qObs k φ) c - pair L φ (q k c)

/-- Canonical pullback and chain aggregation are exactly adjoint, independently
of whether aggregation commutes with boundary. -/
@[simp] theorem pairingDefect_gradedPullback_eq_zero {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k)
    (k : ℕ) (φ : Cochain L k) (c : K.Chain k) :
    pairingDefect q (gradedPullback q) k φ c = 0 := by
  simp [pairingDefect, gradedPullback, pair]

/-- Failure of a declared observation transport to commute with coboundary. -/
def coboundaryTransportDefect {K L : GradedComplex R}
    (qObs : ∀ k, Cochain L k →ₗ[R] Cochain K k)
    (k : ℕ) (φ : Cochain L k) : Cochain K (k + 1) :=
  coboundary K k (qObs k φ) - qObs (k + 1) (coboundary L k φ)

/-- For canonical pullback, the coboundary-transport defect is precisely dual
to the boundary defect.  An arbitrary observation transport need not enjoy
this relation. -/
theorem pair_coboundaryTransportDefect_gradedPullback
    {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k)
    (k : ℕ) (φ : Cochain L k) (c : K.Chain (k + 1)) :
    pair K
        (coboundaryTransportDefect (gradedPullback q) k φ) c =
      pair L φ (boundaryDefect q k c) := by
  change φ (q k (K.boundary k c)) -
      φ (L.boundary k (q (k + 1) c)) =
    φ (q k (K.boundary k c) - L.boundary k (q (k + 1) c))
  exact (map_sub φ _ _).symm

/-- Failure of a declared task observable to be preserved by aggregation. -/
def taskDefect {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k) (k : ℕ)
    (JFine : Cochain K k) (JCoarse : Cochain L k) (c : K.Chain k) : R :=
  pair L JCoarse (q k c) - pair K JFine c

/-- Task mismatch decomposes into failure of pairing duality plus the mismatch
between the declared fine task and the transported coarse task. -/
theorem taskDefect_eq_neg_pairingDefect_add {K L : GradedComplex R}
    (q : ∀ k, K.Chain k →ₗ[R] L.Chain k)
    (qObs : ∀ k, Cochain L k →ₗ[R] Cochain K k)
    (k : ℕ) (JFine : Cochain K k) (JCoarse : Cochain L k)
    (c : K.Chain k) :
    taskDefect q k JFine JCoarse c =
      -pairingDefect q qObs k JCoarse c +
        pair K (qObs k JCoarse - JFine) c := by
  change JCoarse (q k c) - JFine c =
    -(qObs k JCoarse c - JCoarse (q k c)) +
      (qObs k JCoarse c - JFine c)
  abel

/-- A chain complex used to witness that the three defect notions are
logically independent.  Every chain group is `ℤ` and every boundary is zero. -/
def integerZeroComplex : GradedComplex ℤ where
  Chain _ := ℤ
  boundary _ := 0
  boundary_boundary := by simp

/-- Identity aggregation on `integerZeroComplex`. -/
def integerIdentityMap :
    ∀ k, integerZeroComplex.Chain k →ₗ[ℤ] integerZeroComplex.Chain k :=
  fun _ => LinearMap.id

/-- A deliberately wrong observation transport: it discards every cochain. -/
def integerZeroObservationMap :
    ∀ k, Cochain integerZeroComplex k →ₗ[ℤ] Cochain integerZeroComplex k :=
  fun _ => 0

/-- The unit chain in degree zero of `integerZeroComplex`. -/
def integerOneChain : integerZeroComplex.Chain 0 := by
  change ℤ
  exact 1

/-- Exact boundary transport does not force an independently declared
observation transport to preserve the pairing. -/
theorem boundary_exact_but_pairing_defective :
    (∀ k, boundaryDefect integerIdentityMap k = 0) ∧
      pairingDefect integerIdentityMap integerZeroObservationMap 0
        (LinearMap.id : ℤ →ₗ[ℤ] ℤ) integerOneChain ≠ 0 := by
  constructor
  · intro k
    apply (boundaryDefect_eq_zero_iff integerIdentityMap k).2
    intro c
    change (0 : ℤ) = 0
    rfl
  · change (-(1 : ℤ)) ≠ 0
    norm_num

/-- Even exact canonical pairing transport does not preserve a separately
declared task observable. -/
theorem pairing_exact_but_task_defective :
    (∀ (φ : Cochain integerZeroComplex 0)
        (c : integerZeroComplex.Chain 0),
      pairingDefect integerIdentityMap (gradedPullback integerIdentityMap)
        0 φ c = 0) ∧
      taskDefect integerIdentityMap 0 0
        (LinearMap.id : ℤ →ₗ[ℤ] ℤ) integerOneChain ≠ 0 := by
  constructor
  · intro φ c
    exact pairingDefect_gradedPullback_eq_zero integerIdentityMap 0 φ c
  · change (1 : ℤ) ≠ 0
    norm_num

/-- A free cellular chain complex with constant coefficients.  Each degree is
the free `R`-module on its cells; the supplied boundary maps encode oriented
incidence numbers. -/
structure CellularComplex (R : Type v) [CommRing R] where
  Cell : ℕ → Type u
  boundary : ∀ k, (Cell (k + 1) →₀ R) →ₗ[R] (Cell k →₀ R)
  boundary_boundary : ∀ k (c : Cell (k + 2) →₀ R),
    boundary k (boundary (k + 1) c) = 0

/-- Regard a constant-coefficient cellular complex as a graded chain complex. -/
noncomputable def CellularComplex.toGradedComplex
    (K : CellularComplex R) : GradedComplex R where
  Chain k := K.Cell k →₀ R
  boundary := K.boundary
  boundary_boundary := K.boundary_boundary

/-- The incidence column of a cell is its cellular boundary. -/
noncomputable def CellularComplex.incidence (K : CellularComplex R) (k : ℕ)
    (σ : K.Cell (k + 1)) : K.Cell k →₀ R :=
  K.boundary k (Finsupp.single σ 1)

/-- The incidence boundary of every cell is a cycle.  This is the cellular
column form of `boundary ∘ boundary = 0`. -/
theorem CellularComplex.boundary_incidence_eq_zero (K : CellularComplex R)
    (k : ℕ) (σ : K.Cell (k + 2)) :
    K.boundary k (K.incidence (k + 1) σ) = 0 := by
  exact K.boundary_boundary k (Finsupp.single σ 1)

end HigherStokes
end HardProblems
