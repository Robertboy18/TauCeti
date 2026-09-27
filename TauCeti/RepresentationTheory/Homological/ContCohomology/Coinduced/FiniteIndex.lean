/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro

/-!
# Coinduction along a subgroup of finite index

For a subgroup `U` of a topological group `G` and a `U`-module `A`, an element of the coinduced
module `Coind_U^G A` of `TauCeti.DiscreteCoind` is determined by its values on a right transversal
of `U`, since `f (u * g) = u • f g`. When `U` has finite index and `A` is finite this makes
`Coind_U^G A` finite. When moreover `U` is open and acts trivially on `A`, every function on the
coset space extends: `Coind_U^G A` is the module of *all* functions `G ⧸ U → A`, read through
`g ↦ g⁻¹` because the coinduced functions are constant on right cosets while `G ⧸ U` is the space
of left cosets. This is the permutation module `A[G ⧸ U]`, of order `|A| ^ [G : U]`.

Through Shapiro's lemma the finiteness statement makes cohomological vanishing hereditary: if
`H²(G, M)` vanishes for every finite discrete `p`-primary `G`-module `M`, then `H²(U, A)` vanishes
for every finite discrete `p`-primary `U`-module `A` and every open subgroup `U` of a profinite
group `G`, because `H²(U, A) ≅ H²(G, Coind_U^G A)` and `Coind_U^G A` is again finite and
`p`-primary.

## Main definitions

* `TauCeti.DiscreteCoind.quotientPiAddEquiv`: for an open `U` acting trivially on `A`, the
  additive equivalence `Coind_U^G A ≃+ (G ⧸ U → A)`; `quotientPiAddEquiv_smul_apply` records that
  it carries the action of `G` on `Coind_U^G A` to the permutation action on `G ⧸ U → A`.

## Main results

* `TauCeti.DiscreteCoind.apply_out_inv_injective` and `TauCeti.DiscreteCoind.instFinite`:
  restriction to a right transversal is injective, so `Coind_U^G A` is finite for finite `A` and
  finite-index `U`.
* `TauCeti.DiscreteCoind.natCard_of_isOpen`: `|Coind_U^G A| = |A| ^ [G : U]` for an open
  finite-index `U` acting trivially on `A`.
* `TauCeti.ContCohomology.subsingleton_H2_of_isOpen`: vanishing of `H²` on finite discrete
  `p`-primary modules passes to open subgroups of a profinite group.
-/

public section

namespace TauCeti

universe u v

namespace DiscreteCoind

section Transversal

variable {G : Type u} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A : Type v} [AddCommGroup A] [DistribMulAction U A]

/-- **Restriction to a right transversal is injective.** An element of `Coind_U^G A` is determined
by its values at the representatives `(Quotient.out x)⁻¹`, `x : G ⧸ U`, which form a right
transversal of `U` in `G`. -/
theorem apply_out_inv_injective :
    Function.Injective fun (f : DiscreteCoind G U A) (x : G ⧸ U) => f (Quotient.out x)⁻¹ := by
  intro f f' h
  ext g
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g⁻¹
  have hg : g = (u : G) * ((QuotientGroup.mk g⁻¹ : G ⧸ U).out)⁻¹ := by
    rw [hu, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have h' := congrFun h (QuotientGroup.mk g⁻¹)
  simp only at h'
  rw [hg, apply_mul, apply_mul, h']

/-- `Coind_U^G A` is finite when `A` is finite and `U` has finite index. -/
instance instFinite [Finite A] [U.FiniteIndex] : Finite (DiscreteCoind G U A) :=
  Finite.of_injective _ apply_out_inv_injective

end Transversal

section Trivial

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
  {A : Type v} [AddCommGroup A] [DistribMulAction U A]

variable (G U A) in
/-- **The coinduced module of a trivial module along an open subgroup is the permutation
module.** For an open subgroup `U` acting trivially on `A`, the coinduced module `Coind_U^G A` is
the module of all functions `G ⧸ U → A`: a coinduced function is constant on the right cosets of
`U`, and `g ↦ g⁻¹` matches right cosets with the left cosets that make up `G ⧸ U`. -/
def quotientPiAddEquiv (hU : IsOpen (U : Set G)) (htriv : ∀ (u : U) (a : A), u • a = a) :
    DiscreteCoind G U A ≃+ (G ⧸ U → A) where
  toFun f := Quotient.lift (fun g : G => f g⁻¹) fun a b hab => by
    have hab' : a⁻¹ * b ∈ U := QuotientGroup.leftRel_apply.1 hab
    have hb : b⁻¹ = ((⟨(a⁻¹ * b)⁻¹, U.inv_mem hab'⟩ : U) : G) * a⁻¹ := by
      rw [Subgroup.coe_mk, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [hb, apply_mul, htriv]
  invFun φ := mk G U A (fun g => φ (QuotientGroup.mk g⁻¹))
    (by
      have := QuotientGroup.discreteTopology hU
      exact ((IsLocallyConstant.iff_continuous fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ U)).2
        (continuous_quot_mk.comp continuous_inv)).comp φ)
    (fun u g => by rw [mul_inv_rev, QuotientGroup.mk_mul_of_mem _ (U.inv_mem u.2), htriv])
  left_inv f := ext fun g => by
    rw [mk_apply]
    exact congrArg f (inv_inv g)
  right_inv φ := funext fun x => by
    induction x using QuotientGroup.induction_on with
    | H g => exact congrArg φ (congrArg _ (inv_inv g))
  map_add' f f' := funext fun x => by
    induction x using QuotientGroup.induction_on with
    | H g => exact congrFun (coe_add f f') g⁻¹

variable (hU : IsOpen (U : Set G)) (htriv : ∀ (u : U) (a : A), u • a = a)

/-- `quotientPiAddEquiv` reads a coinduced function at the inverse of a coset representative. -/
@[simp]
theorem quotientPiAddEquiv_apply_mk (f : DiscreteCoind G U A) (g : G) :
    quotientPiAddEquiv G U A hU htriv f (QuotientGroup.mk g) = f g⁻¹ := (rfl)

/-- The inverse of `quotientPiAddEquiv` sends `φ : G ⧸ U → A` to the coinduced function
`g ↦ φ (g⁻¹ U)`. -/
@[simp]
theorem quotientPiAddEquiv_symm_apply (φ : G ⧸ U → A) (g : G) :
    (quotientPiAddEquiv G U A hU htriv).symm φ g = φ (QuotientGroup.mk g⁻¹) := (rfl)

/-- **`quotientPiAddEquiv` is `G`-equivariant.** The action `(g • f) x = f (x * g)` of `G` on
`Coind_U^G A` corresponds to the permutation action `(g • φ) y = φ (g⁻¹ • y)` on `G ⧸ U → A`, for
the translation action of `G` on the coset space `G ⧸ U`. -/
@[simp]
theorem quotientPiAddEquiv_smul_apply (g : G) (f : DiscreteCoind G U A) (y : G ⧸ U) :
    quotientPiAddEquiv G U A hU htriv (g • f) y =
      quotientPiAddEquiv G U A hU htriv f (g⁻¹ • y) := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, quotientPiAddEquiv_apply_mk,
      quotientPiAddEquiv_apply_mk, coe_smul, mul_inv_rev, inv_inv]

include hU htriv in
/-- **The order of the coinduced module of a trivial module.** For an open subgroup `U` of finite
index acting trivially on `A`, `Coind_U^G A` has `|A| ^ [G : U]` elements. -/
theorem natCard_of_isOpen [U.FiniteIndex] :
    Nat.card (DiscreteCoind G U A) = Nat.card A ^ U.index := by
  rw [Nat.card_congr (quotientPiAddEquiv G U A hU htriv).toEquiv, Nat.card_fun, U.index_eq_card]

end Trivial

end DiscreteCoind

namespace ContCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {U : Subgroup G} {p : ℕ}

/-- **Vanishing of `H²` on finite `p`-primary coefficients passes to open subgroups.** Let `G` be
a profinite group whose explicit `H²(G, M)` vanishes for every finite discrete `p`-primary
`G`-module `M`, and let `U` be an open subgroup. Then `H²(U, A)` vanishes for every finite discrete
`p`-primary `U`-module `A`, by Shapiro's lemma `H²(U, A) ≅ H²(G, Coind_U^G A)`. -/
theorem subsingleton_H2_of_isOpen (hU : IsOpen (U : Set G))
    (h : ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
      Subsingleton (H2 G M))
    (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction U A] [ContinuousSMul U A] [Finite A] (hA : IsPPrimaryTorsion p A) :
    Subsingleton (H2 U A) := by
  have : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have := h (DiscreteCoind G U A) (isPPrimaryTorsion_discreteCoind G U A hA)
  exact (explicitShapiro2 G U A (Subgroup.isClosed_of_isOpen U hU)).toEquiv.symm.subsingleton

end ContCohomology

end TauCeti
