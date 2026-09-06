import Mathlib

/-!
This snippet is about:

  DirectedComplex
  ComplexMap
  ZeroCochain
  OneCochain
  ZeroChain
  OneChain
  pair
  coboundary
  boundary
  pushForward
  discrete_stokes
  pair_coboundary_eq_zero_of_boundary_eq_zero
  coboundary_natural
  boundary_natural
  path_stokes

found at line 157 of 168, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/DiscreteStokes.lean -/


/-!
# Constant-coefficient sheaf--cosheaf boundary accounting

This module supplies the smallest honest Stokes layer used by the book.  A
directed one-dimensional complex is the incidence space.  Functions on its
vertices and edges are cochains for the constant cellular sheaf.  Finitely
supported vertex and edge flows are chains for the constant cellular
cosheaf.  Coboundary takes endpoint differences, boundary records net
endpoint flow, and their pairing satisfies discrete Stokes.

The construction is deliberately narrower than a general sheaf semantics for
admissible behaviors.  It proves neither restriction closure nor gluing for an
arbitrary behavior assignment; `Behavioral.admissible_glue_counterexample`
shows why those obligations cannot be inferred from the vocabulary alone.
-/

namespace HardProblems
namespace DiscreteStokes

open scoped BigOperators

universe u v

/-- A directed one-dimensional cell complex. Parallel edges and loops are
allowed. -/
structure DirectedComplex where
  Vertex : Type u
  Edge : Type u
  source : Edge → Vertex
  target : Edge → Vertex

/-- A map of directed complexes. It may identify vertices or edges, as a
coarse-graining does, but it must preserve incidence. -/
structure ComplexMap (K L : DirectedComplex) where
  onVertex : K.Vertex → L.Vertex
  onEdge : K.Edge → L.Edge
  map_source : ∀ e, onVertex (K.source e) = L.source (onEdge e)
  map_target : ∀ e, onVertex (K.target e) = L.target (onEdge e)

variable (K : DirectedComplex) (R : Type v) [CommRing R]

/-- Vertex observables: zero-cochains for the constant cellular sheaf. -/
abbrev ZeroCochain := K.Vertex → R

/-- Edge observables: one-cochains for the constant cellular sheaf. -/
abbrev OneCochain := K.Edge → R

/-- Finitely supported vertex flows: zero-chains for the constant cellular
cosheaf. -/
abbrev ZeroChain := K.Vertex →₀ R

/-- Finitely supported edge flows: one-chains for the constant cellular
cosheaf. -/
abbrev OneChain := K.Edge →₀ R

/-- Pair a cochain with a finitely supported chain. -/
def pair {X : Type*} (f : X → R) (c : X →₀ R) : R :=
  c.sum fun x a ↦ a * f x

/-- The constant-sheaf coboundary of a vertex observable. -/
def coboundary (f : ZeroCochain K R) : OneCochain K R :=
  fun e ↦ f (K.target e) - f (K.source e)

/-- The constant-cosheaf boundary of a finitely supported edge flow. -/
noncomputable def boundary (c : OneChain K R) : ZeroChain K R :=
  c.sum fun e a ↦
    Finsupp.single (K.target e) a - Finsupp.single (K.source e) a

/-- Aggregate a finitely supported chain along a possibly many-to-one map. -/
noncomputable def pushForward {X Y : Type*} (q : X → Y) (c : X →₀ R) : Y →₀ R :=
  Finsupp.mapDomain q c

/-- Discrete Stokes with constant coefficients: accumulated interior change
equals the observable evaluated on net boundary flow. -/
theorem discrete_stokes (f : ZeroCochain K R) (c : OneChain K R) :
    pair R (coboundary K R f) c = pair R f (boundary K R c) := by
  classical
  unfold pair boundary coboundary
  rw [Finsupp.sum_sum_index]
  · apply Finsupp.sum_congr
    intro e _
    rw [Finsupp.sum_sub_index (fun _ _ _ ↦ sub_mul _ _ _)]
    simp [mul_sub]
  · intro vertex
    simp
  · intro vertex a b
    simp [add_mul]

/-- A flow with no exposed boundary pairs to zero with every exact local
change. This is the closed-cycle corollary of discrete Stokes. -/
theorem pair_coboundary_eq_zero_of_boundary_eq_zero
    (f : ZeroCochain K R) (c : OneChain K R)
    (hc : boundary K R c = 0) :
    pair R (coboundary K R f) c = 0 := by
  rw [discrete_stokes K R f c, hc]
  simp [pair]

/-- Pulling back a coarse observable and then taking its coboundary is the
same as taking the coarse coboundary and pulling it back to fine edges. -/
theorem coboundary_natural {L : DirectedComplex} (F : ComplexMap K L)
    (f : ZeroCochain L R) :
    coboundary K R (f ∘ F.onVertex) = coboundary L R f ∘ F.onEdge := by
  funext e
  simp [coboundary, F.map_source, F.map_target]

/-- Net boundary flow commutes with incidence-preserving coarse-graining. -/
theorem boundary_natural {L : DirectedComplex} (F : ComplexMap K L)
    (c : OneChain K R) :
    pushForward R F.onVertex (boundary K R c) =
      boundary L R (pushForward R F.onEdge c) := by
  classical
  unfold pushForward boundary
  change (Finsupp.mapDomain.addMonoidHom F.onVertex)
      (c.sum fun e a ↦
        Finsupp.single (K.target e) a - Finsupp.single (K.source e) a) = _
  rw [map_finsuppSum (Finsupp.mapDomain.addMonoidHom F.onVertex) c,
    Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro e _
    simp [Finsupp.mapDomain_sub, F.map_source, F.map_target]
  · intro e
    simp
  · intro e a b
    simp [add_sub_add_comm]

/-- The path form of one-dimensional Stokes: exact local increments telescope
to the difference of the endpoint potentials. -/
theorem path_stokes (potential : K.Vertex → R) (x : ℕ → K.Vertex) (n : ℕ) :
    ∑ i ∈ Finset.range n,
        (potential (x (i + 1)) - potential (x i)) =
      potential (x n) - potential (x 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

end DiscreteStokes
end HardProblems
