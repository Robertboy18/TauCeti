/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.LocalDegree
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The degree of a holomorphic map between compact Riemann surfaces

Let `f : X → Y` be a holomorphic map between Riemann surfaces which is constant near no point of
`X`. Its **fibre sum** at `y : Y` is the number of preimages of `y` counted with local
multiplicities, `TauCeti.RiemannSurface.fiberMultiplicitySum f y = ∑ᶠ x ∈ f ⁻¹' {y},
localMultiplicity f x`. When `X` is compact every fibre is finite, and the fibre sum is a locally
constant function of `y`: the local fibre count `exists_nhds_localMultiplicity_fiber_sum` gives,
at each of the finitely many points of a fibre, a neighbourhood on which nearby fibres carry
exactly the multiplicity of that point, while compactness of the complement of these
neighbourhoods keeps nearby fibres from having any further points. Over a connected `Y` the fibre
sum is therefore the same at every point, and this common value is the **degree**
`TauCeti.RiemannSurface.degree f`. The degree is positive, dominates every local multiplicity,
forces `f` to be surjective, and is multiplicative under composition. Along the way the map is
shown to be open, which is the open mapping theorem for Riemann surfaces.

Nonconstancy is spelled pointwise, as `∀ x, ¬ EventuallyConst f (𝓝 x)`, exactly as in the local
fibre count: this is the hypothesis the arguments use, and on a connected `X` it is equivalent to
`f` being nonconstant by the identity theorem, which is not part of this file. The degree is
defined for every map `f : X → Y` as the supremum of its fibre sums, so that no point of `Y` needs
to be chosen; for a map with constant fibre sums this is that constant, and for other maps the
value is junk.

## Main declarations

* `TauCeti.RiemannSurface.isOpenMap_of_forall_not_eventuallyConst`: the open mapping theorem.
* `TauCeti.RiemannSurface.finite_preimage_singleton`: fibre finiteness over a compact source.
* `TauCeti.RiemannSurface.fiberMultiplicitySum`: the fibre sum of local multiplicities, and
  `TauCeti.RiemannSurface.eventually_fiberMultiplicitySum_eq`, its local constancy.
* `TauCeti.RiemannSurface.degree`: the degree, with
  `TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree` saying that every fibre sum over a
  connected target equals it, `TauCeti.RiemannSurface.degree_pos`,
  `TauCeti.RiemannSurface.surjective_of_forall_not_eventuallyConst` and
  `TauCeti.RiemannSurface.degree_comp`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §2 (Theorem 2.7, the open mapping theorem) and §4 (Theorem 4.24, the degree).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4, Proposition 4.8.
-/

public noncomputable section

open Filter Function Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] {f : X → Y} {g : Y → Z}

/-! ### The fibre sum -/

/-- The number of preimages of `y` under `f`, counted with local multiplicities: the sum of
`TauCeti.RiemannSurface.localMultiplicity f x` over the fibre `f ⁻¹' {y}`. It is `0` when the
fibre is infinite, by the convention for `finsum`.

For a holomorphic `f` on a compact Riemann surface which is constant near no point, this is a
locally constant function of `y` (`TauCeti.RiemannSurface.eventually_fiberMultiplicitySum_eq`), and
over a connected target it is the degree of `f`
(`TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree`). -/
def fiberMultiplicitySum (f : X → Y) (y : Y) : ℕ := ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity f x

theorem fiberMultiplicitySum_def (f : X → Y) (y : Y) :
    fiberMultiplicitySum f y = ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity f x :=
  (rfl)

/-- Over a finite fibre, the fibre sum is a finite sum. -/
theorem fiberMultiplicitySum_eq_sum {y : Y} (hy : (f ⁻¹' {y}).Finite) :
    fiberMultiplicitySum f y = ∑ x ∈ hy.toFinset, localMultiplicity f x :=
  finsum_mem_eq_finite_toFinset_sum _ hy

/-- Each local multiplicity at a point of a finite fibre is at most the fibre sum. -/
theorem localMultiplicity_le_fiberMultiplicitySum {x : X} {y : Y} (hy : (f ⁻¹' {y}).Finite)
    (hx : f x = y) : localMultiplicity f x ≤ fiberMultiplicitySum f y := by
  rw [fiberMultiplicitySum_eq_sum hy]
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (hy.mem_toFinset.2 hx)

/-- The **degree** of a map `f : X → Y` between Riemann surfaces: the supremum of its fibre sums
`TauCeti.RiemannSurface.fiberMultiplicitySum f y`. For `f` holomorphic and constant near no point
of a compact `X`, with `Y` connected, every fibre sum equals the degree
(`TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree`): the degree is the number of preimages
of any point, counted with local multiplicities. The supremum only avoids choosing a point of
`Y`; for maps whose fibre sums are not constant the value is junk. -/
def degree (f : X → Y) : ℕ := ⨆ y, fiberMultiplicitySum f y

theorem degree_def (f : X → Y) : degree f = ⨆ y, fiberMultiplicitySum f y :=
  (rfl)

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-! ### The open mapping theorem -/

/-- **The open mapping theorem, at a point.** A map holomorphic and nonconstant near `x` sends
every neighbourhood of `x` onto a neighbourhood of `f x`. -/
theorem nhds_le_map_nhds_of_not_eventuallyConst {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (hne : ¬ EventuallyConst f (𝓝 x)) :
    𝓝 (f x) ≤ map f (𝓝 x) := by
  intro s hs
  obtain ⟨U, -, hUs, V, hV, -, hfib⟩ :=
    exists_nhds_localMultiplicity_fiber_sum hf hne (mem_map.1 hs)
  refine mem_of_superset hV fun y' hy' ↦ ?_
  obtain ⟨x', hx'⟩ := nonempty_iff_ne_empty.2 (hfib y' hy').1
  have hfx' : f x' = y' := hx'.1
  exact hfx' ▸ hUs hx'.2

/-- **The open mapping theorem.** A holomorphic map between Riemann surfaces which is constant
near no point is an open map. -/
theorem isOpenMap_of_forall_not_eventuallyConst (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x ↦
    nhds_le_map_nhds_of_not_eventuallyConst (.of_forall fun y ↦ hf y) (hne x)

/-- If `f` is holomorphic and nonconstant near `x` and `g` is not constant near `f x`, then
`g ∘ f` is not constant near `x`: by the open mapping theorem, constancy of `g ∘ f` near `x`
would force constancy of `g` on the neighbourhood `f '' U` of `f x`. -/
theorem not_eventuallyConst_comp {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (hne : ¬ EventuallyConst f (𝓝 x))
    (hg : ¬ EventuallyConst g (𝓝 (f x))) : ¬ EventuallyConst (g ∘ f) (𝓝 x) := fun h ↦ by
  have : Nonempty Z := ⟨g (f x)⟩
  obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 h
  refine hg (eventuallyConst_iff_exists_eventuallyEq.2 ⟨c, ?_⟩)
  exact Eventually.filter_mono (nhds_le_map_nhds_of_not_eventuallyConst hf hne)
    (eventually_map.2 hc)

/-! ### Fibre finiteness -/

/-- **Finiteness of fibres.** A holomorphic map from a compact Riemann surface which is constant
near no point has finite fibres: each fibre is compact, and each of its points has a neighbourhood
containing no other point of the fibre. -/
theorem finite_preimage_singleton [CompactSpace X] [T1Space Y]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  have hK : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf.continuous).isCompact
  have hloc : ∀ x ∈ f ⁻¹' {y}, ∃ U ∈ 𝓝 x, f ⁻¹' {f x} ∩ U = {x} := fun x _ ↦ by
    obtain ⟨U, hU, -, V, -, hx, -⟩ :=
      exists_nhds_localMultiplicity_fiber_sum (.of_forall fun z ↦ hf z) (hne x) univ_mem
    exact ⟨U, hU, hx⟩
  choose! U hU hUx using hloc
  obtain ⟨t, hts, ht⟩ := hK.elim_nhds_subcover U hU
  refine t.finite_toSet.subset fun x' hx' ↦ ?_
  obtain ⟨x, hxt, hx'U⟩ := mem_iUnion₂.1 (ht hx')
  have hx : x ∈ f ⁻¹' {y} := hts x hxt
  have hx'x : x' ∈ f ⁻¹' {f x} ∩ U x := by
    refine ⟨?_, hx'U⟩
    rw [mem_preimage, mem_singleton_iff] at hx hx' ⊢
    rw [hx', hx]
  rw [hUx x hx, mem_singleton_iff] at hx'x
  rw [hx'x]
  exact Finset.mem_coe.2 hxt

/-! ### Local constancy of the fibre sum -/

/-- **Local constancy of the fibre sum.** For a holomorphic map from a compact Riemann surface
which is constant near no point, the fibre sum of local multiplicities is the same at every point
near `y` as at `y`. -/
theorem eventually_fiberMultiplicitySum_eq [CompactSpace X] [T2Space X] [T2Space Y]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) (y : Y) :
    ∀ᶠ y' in 𝓝 y, fiberMultiplicitySum f y' = fiberMultiplicitySum f y := by
  have hS : (f ⁻¹' {y}).Finite := finite_preimage_singleton hf hne y
  -- Pairwise disjoint open neighbourhoods of the finitely many points of the fibre of `y`.
  obtain ⟨O, hO, hOdisj⟩ := hS.t2_separation
  -- The local fibre count at each point of the fibre, inside those neighbourhoods.
  have hloc : ∀ x ∈ f ⁻¹' {y}, ∃ U ∈ 𝓝 x, U ⊆ O x ∧ ∃ V ∈ 𝓝 y, ∀ y' ∈ V,
      (f ⁻¹' {y'} ∩ U).Finite ∧
      (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ U, localMultiplicity f x') = localMultiplicity f x := by
    intro x hx
    have hfx : f x = y := hx
    obtain ⟨U, hU, hUO, V, hV, -, hcount⟩ := exists_nhds_localMultiplicity_fiber_sum
      (.of_forall fun z ↦ hf z) (hne x) ((hO x).2.mem_nhds (hO x).1)
    exact ⟨U, hU, hUO, V, hfx ▸ hV, fun y' hy' ↦ ⟨(hcount y' hy').2.1, (hcount y' hy').2.2⟩⟩
  choose! U hU hUO V hV hcount using hloc
  -- Outside the interiors of the `U x` the map misses `y`, hence a whole neighbourhood of `y`.
  have hK : IsCompact (⋃ x ∈ f ⁻¹' {y}, interior (U x))ᶜ :=
    (isOpen_biUnion fun x _ ↦ isOpen_interior).isClosed_compl.isCompact
  have hyK : y ∉ f '' (⋃ x ∈ f ⁻¹' {y}, interior (U x))ᶜ := by
    rintro ⟨x, hxK, hfx⟩
    exact hxK (mem_iUnion₂.2 ⟨x, hfx, mem_interior_iff_mem_nhds.2 (hU x hfx)⟩)
  have hV₀ : (f '' (⋃ x ∈ f ⁻¹' {y}, interior (U x))ᶜ)ᶜ ∈ 𝓝 y :=
    (hK.image hf.continuous).isClosed.isOpen_compl.mem_nhds hyK
  filter_upwards [hV₀, (biInter_mem hS).2 hV] with y' hy'₀ hy'V
  have hy'V' : ∀ x ∈ f ⁻¹' {y}, y' ∈ V x := mem_iInter₂.1 hy'V
  -- The fibre of `y'` is the disjoint union of its pieces inside the `U x`.
  have hfib : f ⁻¹' {y'} = ⋃ x ∈ f ⁻¹' {y}, (f ⁻¹' {y'} ∩ U x) := by
    ext x'
    refine ⟨fun hx' ↦ ?_, fun hx' ↦ ?_⟩
    · have hx'U : x' ∈ ⋃ x ∈ f ⁻¹' {y}, interior (U x) := by
        by_contra h
        exact hy'₀ ⟨x', h, hx'⟩
      obtain ⟨x, hx, hx'U⟩ := mem_iUnion₂.1 hx'U
      exact mem_iUnion₂.2 ⟨x, hx, hx', interior_subset hx'U⟩
    · obtain ⟨x, -, hx'⟩ := mem_iUnion₂.1 hx'
      exact hx'.1
  have hdisj : (f ⁻¹' {y}).PairwiseDisjoint fun x ↦ f ⁻¹' {y'} ∩ U x :=
    hOdisj.mono_on fun x hx ↦ inter_subset_right.trans (hUO x hx)
  simp only [fiberMultiplicitySum_def]
  rw [hfib, finsum_mem_biUnion hdisj hS fun x hx ↦ (hcount x hx y' (hy'V' x hx)).1]
  exact finsum_mem_congr rfl fun x hx ↦ (hcount x hx y' (hy'V' x hx)).2

/-- For a holomorphic map from a compact Riemann surface which is constant near no point, the
fibre sum of local multiplicities is a locally constant function on the target. -/
theorem isLocallyConstant_fiberMultiplicitySum [CompactSpace X] [T2Space X] [T2Space Y]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) :
    IsLocallyConstant (fiberMultiplicitySum f) :=
  (IsLocallyConstant.iff_eventually_eq _).2 (eventually_fiberMultiplicitySum_eq hf hne)

/-! ### The degree -/

section Degree

variable [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]
  (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x))
include hf hne

/-- **Fibre independence of the degree.** For a holomorphic map from a compact Riemann surface to
a connected Riemann surface which is constant near no point, the number of preimages of any point
counted with local multiplicities is the degree. -/
theorem fiberMultiplicitySum_eq_degree (y : Y) : fiberMultiplicitySum f y = degree f := by
  have : Nonempty Y := ⟨y⟩
  have h : fiberMultiplicitySum f = fun _ ↦ fiberMultiplicitySum f y :=
    funext fun y' ↦ (isLocallyConstant_fiberMultiplicitySum hf hne).apply_eq_of_preconnectedSpace
      y' y
  rw [degree_def, h, ciSup_const]

/-- The degree is the sum of the local multiplicities over any fibre, as a finite sum. -/
theorem degree_eq_sum_localMultiplicity (y : Y) :
    degree f = ∑ x ∈ (finite_preimage_singleton hf hne y).toFinset, localMultiplicity f x :=
  (fiberMultiplicitySum_eq_degree hf hne y).symm.trans (fiberMultiplicitySum_eq_sum _)

/-- Every local multiplicity is at most the degree. -/
theorem localMultiplicity_le_degree (x : X) : localMultiplicity f x ≤ degree f :=
  (localMultiplicity_le_fiberMultiplicitySum (finite_preimage_singleton hf hne (f x)) rfl).trans
    (fiberMultiplicitySum_eq_degree hf hne (f x)).le

/-- **Positivity of the degree.** A holomorphic map from a nonempty compact Riemann surface to a
connected Riemann surface which is constant near no point has positive degree. -/
theorem degree_pos [Nonempty X] : 0 < degree f :=
  ((localMultiplicity_pos_iff (.of_forall fun z ↦ hf z)).2 (hne (Classical.arbitrary X))).trans_le
    (localMultiplicity_le_degree hf hne _)

/-- **Surjectivity.** A holomorphic map from a nonempty compact Riemann surface to a connected
Riemann surface which is constant near no point is surjective: its positive degree is the fibre
sum over every point, so no fibre is empty. -/
theorem surjective_of_forall_not_eventuallyConst [Nonempty X] : Surjective f := fun y ↦ by
  by_contra h
  have hemp : f ⁻¹' {y} = ∅ := eq_empty_iff_forall_notMem.2 fun x hx ↦ h ⟨x, hx⟩
  have h0 : fiberMultiplicitySum f y = 0 := by
    rw [fiberMultiplicitySum_def, hemp, finsum_mem_empty]
  exact (degree_pos hf hne).ne' ((fiberMultiplicitySum_eq_degree hf hne y).symm.trans h0)

end Degree

/-! ### Composition -/

variable [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) 1 Z]

/-- **Multiplicativity of the degree.** For holomorphic maps `f : X → Y` and `g : Y → Z` of
compact Riemann surfaces with connected targets, both constant near no point, the degree of
`g ∘ f` is the product of the degrees: the fibre of `g ∘ f` over `z` is the disjoint union of the
fibres of `f` over the points of the fibre of `g` over `z`, and the local multiplicities
multiply. -/
theorem degree_comp [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [PreconnectedSpace Y] [T2Space Z] [PreconnectedSpace Z]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x))
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hneg : ∀ y, ¬ EventuallyConst g (𝓝 y)) :
    degree (g ∘ f) = degree g * degree f := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z⟩⟩
  · simp [degree_def]
  have hgf : ∀ x, ¬ EventuallyConst (g ∘ f) (𝓝 x) := fun x ↦
    not_eventuallyConst_comp (.of_forall fun w ↦ hf w) (hne x) (hneg (f x))
  have hT : (g ⁻¹' {z}).Finite := finite_preimage_singleton hg hneg z
  -- The fibre of `g ∘ f` over `z` is the disjoint union of the fibres of `f` over `g ⁻¹' {z}`.
  have hfib : (g ∘ f) ⁻¹' {z} = ⋃ y ∈ g ⁻¹' {z}, f ⁻¹' {y} := by
    ext x
    simp
  have hdisj : (g ⁻¹' {z}).PairwiseDisjoint fun y ↦ f ⁻¹' {y} := fun y _ y' _ hyy' ↦
    disjoint_left.2 fun x hx hx' ↦ hyy' ((mem_singleton_iff.1 hx).symm.trans hx')
  rw [← fiberMultiplicitySum_eq_degree (hg.comp hf) hgf z,
    ← fiberMultiplicitySum_eq_degree hg hneg z, fiberMultiplicitySum_def,
    fiberMultiplicitySum_def, hfib,
    finsum_mem_biUnion hdisj hT fun y _ ↦ finite_preimage_singleton hf hne y,
    finsum_mem_eq_finite_toFinset_sum _ hT, finsum_mem_eq_finite_toFinset_sum _ hT, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have hS : (f ⁻¹' {y}).Finite := finite_preimage_singleton hf hne y
  calc ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity (g ∘ f) x
      = ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity g y * localMultiplicity f x :=
        finsum_mem_congr rfl fun x hx ↦ by
          rw [localMultiplicity_comp (.of_forall fun w ↦ hg w) (.of_forall fun w ↦ hf w),
            mem_singleton_iff.1 (mem_preimage.1 hx)]
    _ = localMultiplicity g y * fiberMultiplicitySum f y := by
        rw [fiberMultiplicitySum_eq_sum hS, finsum_mem_eq_finite_toFinset_sum _ hS, Finset.mul_sum]
    _ = localMultiplicity g y * degree f := by rw [fiberMultiplicitySum_eq_degree hf hne y]

end TauCeti.RiemannSurface

end
