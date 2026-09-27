/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Inflation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression

/-!
# Heisenberg cochains: the transgression of a cup product

Let `G` be a topological group, let `M`, `A` and `P` be topological `G`-modules with an equivariant
pairing `μ : M →+ A →+ P`, and let `a` and `b` be continuous `1`-cocycles with values in `M` and
`A`. A **Heisenberg cochain** for `(a, b)` is a continuous `h : G → P` with

```text
h (g * g') = h g + g • h g' + μ (a g) (g • b g'),
```

that is, a continuous `1`-cochain whose coboundary is `-(a ⌣ b)`, for the explicit `(1,1)` cup
product `(a ⌣ b) (g, g') = μ (a g) (g • b g')`. For trivial actions and `μ` the multiplication of
`𝔽_p`, the triple `(a, b, h)` is a homomorphism from `G` to the Heisenberg group of unipotent upper
triangular `3 × 3` matrices over `𝔽_p`, with `a` and `b` on the superdiagonal and `h` in the
corner, which is where the name comes from. Such a cochain exists exactly when the cup product
`a ⌣ b` vanishes in `H²(G, P)` (`TauCeti.ContCohomology.explicitCup11_eq_zero_iff`), in
particular whenever `H²(G, P) = 0`, for instance for a free pro-`p` group and `𝔽_p`-coefficients.

The main theorem is the computation of the transgression through a Heisenberg cochain. Let `N` be a
closed normal subgroup of a profinite group `G` on which `a` and `b` vanish, so that they descend to
cocycles `a'` and `b'` on `G ⧸ N` with values in the `N`-invariants. Then `-h` is a transgression
lift of its restriction `-h|_N`, which is a conjugation-invariant continuous `1`-cocycle on `N`, and

```text
tg [-h|_N] = a' ⌣ b'   in H²(G ⧸ N, P ^ N).
```

When the transgression is bijective, for instance for a minimal presentation `1 → R → F → G → 1` of
a pro-`p` group by a free pro-`p` group `F` and `𝔽_p`-coefficients, this identifies the cup
product `a' ⌣ b' ∈ H²(G, 𝔽_p)` with the character `r ↦ -h r` of `R`; so the value of the cup
product on a relator `r` is `-h r`. The values of `h` on commutators and on powers are recorded for
trivial actions, `h ⁅g, g'⁆ = μ (a g) (b g') - μ (a g') (b g)` and
`h (g ^ n) = n • h g + (n.choose 2) • μ (a g) (b g)`; these are what reads the cup product off the
class of a relator modulo `Fᵖ[F, F]`, as in Labute's Proposition 3.

## Main definitions

* `TauCeti.ContCohomology.IsHeisenbergCochain`: `h` is a Heisenberg cochain for `(a, b)` and `μ`.
* `TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict`: the restriction `-h|_N`, a continuous
  `1`-cocycle on a normal subgroup `N` on which `a` and `b` vanish.

## Main results

* `TauCeti.ContCohomology.explicitCup11_eq_zero_iff`: the `(1,1)` cup product of two cocycles
  vanishes exactly when they admit a Heisenberg cochain
  (`TauCeti.ContCohomology.IsHeisenbergCochain.of_d1_eq` and
  `TauCeti.ContCohomology.IsHeisenbergCochain.d1_neg` are the two directions on cochains), and
  `TauCeti.ContCohomology.exists_isHeisenbergCochain_of_subsingleton_H2`: it exists when
  `H²(G, P) = 0`.
* `TauCeti.ContCohomology.IsHeisenbergCochain.isTransgressionLift`: `-h` is a transgression lift of
  `-h|_N`, and `TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict_mem_H1ConjInvariants`: the
  class of `-h|_N` is conjugation-invariant.
* `TauCeti.ContCohomology.IsHeisenbergCochain.transgression_negRestrict`: **the transgression of
  `-h|_N` is the cup product of the descended cocycles.**
* `TauCeti.ContCohomology.IsHeisenbergCochain.apply_commutatorElement_of_smul_eq_self`,
  `TauCeti.ContCohomology.IsHeisenbergCochain.apply_pow_of_smul_eq_self`: the values of a
  Heisenberg cochain on commutators and on powers, for trivial actions.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1.4
  and Proposition 3.
* W. G. Dwyer, *Homology, Massey products and maps between groups*, J. Pure Appl. Algebra 6
  (1975), 177–190, for the lifting of a pair of characters with vanishing cup product to the
  Heisenberg group.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III,
  §9.
-/

public section

namespace TauCeti.ContCohomology

open scoped commutatorElement

universe uG uM uA uP

section Cochain

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [DistribMulAction G P]
  (μ : M →+ A →+ P)

/-- A **Heisenberg cochain** for the continuous `1`-cocycles `a : G → M` and `b : G → A` and the
pairing `μ : M →+ A →+ P`: a continuous `h : G → P` with
`h (g * g') = h g + g • h g' + μ (a g) (g • b g')`. Equivalently, the coboundary of `-h` is the
explicit `(1,1)` cup product `(a ⌣ b) (g, g') = μ (a g) (g • b g')`
(`TauCeti.ContCohomology.IsHeisenbergCochain.d1_neg`); for trivial actions, `(a, b, h)` is a
homomorphism to the Heisenberg group with `a` and `b` on the superdiagonal and `h` in the corner.
-/
structure IsHeisenbergCochain (a : Z1 G M) (b : Z1 G A) (h : G → P) : Prop where
  /-- the cochain `h` is continuous -/
  continuous : Continuous h
  /-- the Heisenberg multiplication law `h (g * g') = h g + g • h g' + μ (a g) (g • b g')` -/
  apply_mul : ∀ g g' : G, h (g * g') = h g + g • h g' + μ ((a : G → M) g) (g • (b : G → A) g')

namespace IsHeisenbergCochain

variable {μ} {a : Z1 G M} {b : Z1 G A}

/-- **A continuous primitive of the cup cochain gives a Heisenberg cochain**: if `f` is continuous
with `d¹ f = ((g, g') ↦ μ (a g) (g • b g'))`, then `-f` is a Heisenberg cochain for `(a, b)`. -/
theorem of_d1_eq [IsTopologicalAddGroup P] {f : G → P} (hf : Continuous f)
    (hd : d1 G P f = fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → A) q.2)) :
    IsHeisenbergCochain μ a b fun g => -f g where
  continuous := hf.neg
  apply_mul g g' := by
    have e : d1 G P f (g, g') = μ ((a : G → M) g) (g • (b : G → A) g') := congrFun hd (g, g')
    rw [d1_apply] at e
    rw [← e, smul_neg]
    abel

variable {h : G → P} (hh : IsHeisenbergCochain μ a b h)
include hh

/-- The coboundary of `-h` is the `(1,1)` cup cochain `(g, g') ↦ μ (a g) (g • b g')`. -/
theorem d1_neg :
    d1 G P (fun g => -h g) = fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → A) q.2) := by
  funext ⟨g, g'⟩
  dsimp only
  rw [d1_apply, hh.apply_mul, smul_neg]
  abel

/-- A Heisenberg cochain vanishes at `1`. -/
theorem apply_one : h 1 = 0 := by
  have e := hh.apply_mul 1 1
  rwa [mul_one, one_smul, one_smul, groupCohomology.map_one_of_isCocycle₁ (mem_Z1_iff.1 b.2).2,
    map_zero, add_zero, left_eq_add] at e

variable {N : Subgroup G} [N.Normal]

/-- **Conjugation formula.** If `a` and `b` vanish on the normal subgroup `N`, then for `n ∈ N`
`g • h (g⁻¹ * n * g) = h n + n • h g - h g`. -/
theorem apply_conj (haN : ∀ n : N, (a : G → M) n = 0) (hbN : ∀ n : N, (b : G → A) n = 0)
    (g : G) (n : N) : g • h (g⁻¹ * n * g) = h n + (n : G) • h g - h g := by
  have hb1 := (mem_Z1_iff.1 b.2).2
  have hmem : g⁻¹ * n * g ∈ N := by
    simpa only [inv_inv] using ‹N.Normal›.conj_mem n n.2 g⁻¹
  -- `b` is constant on the coset `N * g`, since `n * g = g * (g⁻¹ * n * g)` with the second factor
  -- in `N`.
  have hbng : (b : G → A) (n * g) = (b : G → A) g := by
    rw [show (n : G) * g = g * (g⁻¹ * n * g) by group, hb1, hbN ⟨_, hmem⟩, smul_zero, zero_add]
  have e1 := hh.apply_mul g⁻¹ (n * g)
  have e2 := hh.apply_mul n g
  have e3 := hh.apply_mul g⁻¹ g
  rw [inv_mul_cancel, hh.apply_one] at e3
  rw [haN n, map_zero, AddMonoidHom.zero_apply, add_zero] at e2
  rw [hbng, ← mul_assoc, e2, smul_add] at e1
  -- `h g⁻¹ + μ (a g⁻¹) (g⁻¹ • b g) = -(g⁻¹ • h g)`, from `h 1 = 0`.
  have e4 : h g⁻¹ + μ ((a : G → M) g⁻¹) (g⁻¹ • (b : G → A) g) = -(g⁻¹ • h g) := by
    rw [eq_neg_iff_add_eq_zero]
    calc h g⁻¹ + μ ((a : G → M) g⁻¹) (g⁻¹ • (b : G → A) g) + g⁻¹ • h g
        = h g⁻¹ + g⁻¹ • h g + μ ((a : G → M) g⁻¹) (g⁻¹ • (b : G → A) g) := by abel
      _ = 0 := e3.symm
  rw [e1, show h g⁻¹ + (g⁻¹ • h n + g⁻¹ • ((n : G) • h g)) +
        μ ((a : G → M) g⁻¹) (g⁻¹ • (b : G → A) g) =
      (h g⁻¹ + μ ((a : G → M) g⁻¹) (g⁻¹ • (b : G → A) g)) +
        (g⁻¹ • h n + g⁻¹ • ((n : G) • h g)) by abel,
    e4, smul_add, smul_neg, smul_add, smul_smul, smul_smul, smul_smul, mul_inv_cancel, one_smul,
    one_smul, one_smul]
  abel

variable [IsTopologicalGroup G] [IsTopologicalAddGroup P]

/-- **A Heisenberg cochain is a transgression lift.** If `a` and `b` vanish on the normal subgroup
`N`, then `-h` is a transgression lift of its restriction `-h|_N`. -/
theorem isTransgressionLift (haN : ∀ n : N, (a : G → M) n = 0)
    (hbN : ∀ n : N, (b : G → A) n = 0) :
    IsTransgressionLift (fun n : N => -h n) (fun g => -h g) where
  continuous := hh.continuous.neg
  apply_mul g n := by
    rw [hh.apply_mul, hbN n, smul_zero, map_zero, add_zero, smul_neg]
    abel
  smul_conj_sub g n := by
    rw [d0_apply, Subgroup.smul_def, Subgroup.inverseConjugationHom_apply, Subgroup.coe_mk]
    simp only [smul_neg]
    rw [hh.apply_conj haN hbN g n]
    abel

/-- **The restriction `-h|_N`** of a Heisenberg cochain to a normal subgroup `N` on which `a` and
`b` vanish, a continuous `1`-cocycle on `N`. Its class is conjugation-invariant
(`TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict_mem_H1ConjInvariants`) and transgresses
to the cup product of the descended cocycles
(`TauCeti.ContCohomology.IsHeisenbergCochain.transgression_negRestrict`). -/
def negRestrict (haN : ∀ n : N, (a : G → M) n = 0) (hbN : ∀ n : N, (b : G → A) n = 0) :
    Z1 N P :=
  ⟨fun n : N => -h n, (hh.isTransgressionLift haN hbN).mem_Z1⟩

/-- The restriction `-h|_N`, as a function on `N`. -/
@[simp]
theorem coe_negRestrict (haN : ∀ n : N, (a : G → M) n = 0)
    (hbN : ∀ n : N, (b : G → A) n = 0) :
    (hh.negRestrict haN hbN : N → P) = fun n : N => -h n :=
  (rfl)

/-- The cochain `-h` is a transgression lift of `-h|_N`. -/
theorem negRestrict_isTransgressionLift (haN : ∀ n : N, (a : G → M) n = 0)
    (hbN : ∀ n : N, (b : G → A) n = 0) :
    IsTransgressionLift ((hh.negRestrict haN hbN : Z1 N P) : N → P) (fun g => -h g) := by
  rw [coe_negRestrict]
  exact hh.isTransgressionLift haN hbN

variable [ContinuousSMul G P]

/-- The class of `-h|_N` in `H¹(N, P)` is conjugation-invariant. -/
theorem negRestrict_mem_H1ConjInvariants (haN : ∀ n : N, (a : G → M) n = 0)
    (hbN : ∀ n : N, (b : G → A) n = 0) :
    (hh.negRestrict haN hbN : H1 N P) ∈ H1ConjInvariants G P N :=
  IsTransgressionLift.mk_mem_H1ConjInvariants (hh.negRestrict_isTransgressionLift haN hbN)

end IsHeisenbergCochain

end Cochain

section Existence

variable {G : Type uG} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  {μ : M →+ A →+ P} (hμ : Continuous fun p : M × A => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : A), μ (g • m) (g • x) = g • μ m x)
include hμ hequiv

/-- **A Heisenberg cochain exists exactly when the cup product vanishes**: the explicit `(1,1)` cup
product of the classes of `a` and `b` is zero in `H²(G, P)` if and only if `(a, b)` admits a
Heisenberg cochain. -/
theorem explicitCup11_eq_zero_iff (a : Z1 G M) (b : Z1 G A) :
    explicitCup11 G M A P μ hμ hequiv (a : H1 G M) (b : H1 G A) = 0 ↔
      ∃ h : G → P, IsHeisenbergCochain μ a b h := by
  rw [explicitCup11_mk, H2pi_eq_zero_iff, mem_B2_iff]
  constructor
  · rintro ⟨f, hf, hd⟩
    exact ⟨fun g => -f g, IsHeisenbergCochain.of_d1_eq hf hd⟩
  · rintro ⟨h, hh⟩
    exact ⟨fun g => -h g, hh.continuous.neg, hh.d1_neg⟩

/-- **Heisenberg cochains exist when `H²(G, P)` vanishes**, for instance on a free pro-`p` group
with `𝔽_p`-coefficients. -/
theorem exists_isHeisenbergCochain_of_subsingleton_H2 [Subsingleton (H2 G P)] (a : Z1 G M)
    (b : Z1 G A) : ∃ h : G → P, IsHeisenbergCochain μ a b h :=
  (explicitCup11_eq_zero_iff hμ hequiv a b).1 (Subsingleton.elim _ _)

end Existence

section Transgression

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DiscreteTopology P] [DistribMulAction G P] [ContinuousSMul G P]
  {N : Subgroup G} [N.Normal]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N A)]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N P)]
  {μ : M →+ A →+ P} (hμ : Continuous fun p : M × A => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : A), μ (g • m) (g • x) = g • μ m x)
  {a : Z1 G M} {b : Z1 G A} {h : G → P} (hh : IsHeisenbergCochain μ a b h)
  (hN : IsClosed (N : Set G)) (haN : ∀ n : N, (a : G → M) n = 0)
  (hbN : ∀ n : N, (b : G → A) n = 0)
include hμ hequiv hh hN haN hbN

/-- **The transgression of `-h|_N` is the cup product.** Let `N` be a closed normal subgroup of a
profinite group `G`, let `a` and `b` be continuous `1`-cocycles vanishing on `N`, with descents `a'`
and `b'` to `G ⧸ N` valued in the `N`-invariants, and let `h` be a Heisenberg cochain for `(a, b)`.
Then the transgression `H¹(N, P)^{G ⧸ N} → H²(G ⧸ N, P ^ N)` sends the class of `-h|_N` to the
explicit `(1,1)` cup product `a' ⌣ b'` for the pairing induced by `μ` on the invariants. -/
theorem IsHeisenbergCochain.transgression_negRestrict :
    transgression G P N hN
        ⟨hh.negRestrict haN hbN, hh.negRestrict_mem_H1ConjInvariants haN hbN⟩ =
      explicitCup11 (G ⧸ N) (FixedPoints.addSubgroup N M) (FixedPoints.addSubgroup N A)
        (FixedPoints.addSubgroup N P) (fixedPointsPairing N μ fun n => hequiv (n : G))
        (continuous_fixedPointsPairing N μ (fun n => hequiv (n : G)) hμ)
        (fixedPointsPairing_quotient_smul N μ hequiv) (descendZ1 a haN) (descendZ1 b hbN) := by
  rw [transgression_eq_mk_cocycle G P N hN _ (hh.negRestrict haN hbN) rfl
    (hh.negRestrict_isTransgressionLift haN hbN), explicitCup11_mk]
  refine congrArg (fun z : Z2 (G ⧸ N) (FixedPoints.addSubgroup N P) =>
    (z : H2 (G ⧸ N) (FixedPoints.addSubgroup N P))) (Subtype.ext (funext fun q => ?_))
  obtain ⟨q₁, q₂⟩ := q
  induction q₁ using QuotientGroup.induction_on with
  | H g =>
    induction q₂ using QuotientGroup.induction_on with
    | H g' =>
      refine Subtype.ext ?_
      rw [IsTransgressionLift.coe_cocycle_apply_mk, coe_fixedPointsPairing,
        coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup,
        coe_descendZ1_apply_mk, coe_descendZ1_apply_mk]
      exact congrFun hh.d1_neg (g, g')

end Transgression

section TrivialAction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [DistribMulAction G P]
  {μ : M →+ A →+ P} {a : Z1 G M} {b : Z1 G A} {h : G → P} (hh : IsHeisenbergCochain μ a b h)
  (htrivM : ∀ (g : G) (m : M), g • m = m) (htrivA : ∀ (g : G) (x : A), g • x = x)
  (htrivP : ∀ (g : G) (x : P), g • x = x)

namespace IsHeisenbergCochain

include hh htrivA htrivP in
/-- For trivial actions the Heisenberg law reads `h (g * g') = h g + h g' + μ (a g) (b g')`. -/
theorem apply_mul_of_smul_eq_self (g g' : G) :
    h (g * g') = h g + h g' + μ ((a : G → M) g) ((b : G → A) g') := by
  rw [hh.apply_mul, htrivP, htrivA]

include hh htrivA htrivP in
/-- For trivial actions, `h g⁻¹ = -h g + μ (a g) (b g)`. -/
theorem apply_inv_of_smul_eq_self (g : G) :
    h g⁻¹ = -h g + μ ((a : G → M) g) ((b : G → A) g) := by
  have e := hh.apply_mul_of_smul_eq_self htrivA htrivP g g⁻¹
  have hb : (b : G → A) g⁻¹ = -(b : G → A) g := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← map_mul_of_smul_eq_self_of_mem_Z1 htrivA b.2,
      mul_inv_cancel, groupCohomology.map_one_of_isCocycle₁ (mem_Z1_iff.1 b.2).2]
  rw [mul_inv_cancel, hh.apply_one, hb, map_neg] at e
  rw [eq_neg_add_iff_add_eq, ← sub_eq_zero, sub_eq_add_neg]
  exact e.symm

include hh htrivM htrivA htrivP in
/-- **The value of a Heisenberg cochain on a commutator**, for trivial actions:
`h ⁅g, g'⁆ = μ (a g) (b g') - μ (a g') (b g)`. This is the antisymmetric part of the cup
pairing, read on the commutator `g * g' * g⁻¹ * g'⁻¹`. -/
theorem apply_commutatorElement_of_smul_eq_self (g g' : G) :
    h ⁅g, g'⁆ = μ ((a : G → M) g) ((b : G → A) g') - μ ((a : G → M) g') ((b : G → A) g) := by
  have ha_mul := map_mul_of_smul_eq_self_of_mem_Z1 htrivM a.2
  have hb_mul := map_mul_of_smul_eq_self_of_mem_Z1 htrivA b.2
  have ha_inv : ∀ x : G, (a : G → M) x⁻¹ = -(a : G → M) x := fun x => by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← ha_mul, mul_inv_cancel,
      groupCohomology.map_one_of_isCocycle₁ (mem_Z1_iff.1 a.2).2]
  have hb_inv : ∀ x : G, (b : G → A) x⁻¹ = -(b : G → A) x := fun x => by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← hb_mul, mul_inv_cancel,
      groupCohomology.map_one_of_isCocycle₁ (mem_Z1_iff.1 b.2).2]
  simp only [commutatorElement_def, hh.apply_mul_of_smul_eq_self htrivA htrivP,
    hh.apply_inv_of_smul_eq_self htrivA htrivP, ha_mul, ha_inv, hb_inv, map_add, map_neg,
    AddMonoidHom.add_apply, AddMonoidHom.neg_apply]
  abel

include hh htrivM htrivA htrivP in
/-- **The value of a Heisenberg cochain on a power**, for trivial actions:
`h (g ^ n) = n • h g + (n.choose 2) • μ (a g) (b g)`. This is the symmetric part of the cup
pairing, read on the `n`-th power. -/
theorem apply_pow_of_smul_eq_self (g : G) (n : ℕ) :
    h (g ^ n) = n • h g + (n.choose 2) • μ ((a : G → M) g) ((b : G → A) g) := by
  have ha_mul := map_mul_of_smul_eq_self_of_mem_Z1 htrivM a.2
  have ha_pow : ∀ n : ℕ, (a : G → M) (g ^ n) = n • (a : G → M) g := fun n => by
    induction n with
    | zero => rw [pow_zero, zero_smul, groupCohomology.map_one_of_isCocycle₁ (mem_Z1_iff.1 a.2).2]
    | succ n ih => rw [pow_succ, ha_mul, ih, succ_nsmul]
  induction n with
  | zero =>
    rw [pow_zero, hh.apply_one, zero_smul, Nat.choose_zero_succ, zero_smul, add_zero]
  | succ n ih =>
    rw [pow_succ, hh.apply_mul_of_smul_eq_self htrivA htrivP, ih, ha_pow, map_nsmul,
      AddMonoidHom.nsmul_apply, Nat.choose_succ_succ, Nat.choose_one_right]
    simp only [add_nsmul, one_nsmul]
    abel

end IsHeisenbergCochain

end TrivialAction

end TauCeti.ContCohomology
