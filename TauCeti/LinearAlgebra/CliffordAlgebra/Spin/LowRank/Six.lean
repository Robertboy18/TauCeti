/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import Mathlib.Tactic.Module

/-!
# The Spin group is strictly smaller than the even unitary group in dimension six

For a nondegenerate quadratic form in dimensions one to five, the Spin group is the whole even
unitary group `U(C₀, σ)` of the Clifford algebra: every even Clifford unit `x` with
`reverse x * x = 1` lies in the Lipschitz group. The sibling files prove this in dimensions one
and two. This file shows that the equality stops in dimension six, where `U(C₀, σ)` is a unitary
group of degree four and the Spin group is only its reduced-norm-one subgroup, and that it fails in
every dimension from six on.

The witness is explicit. Let `ω = ι v₁ ⋯ ι v₆` be the volume element of an orthogonal anisotropic
basis. It is even, it anticommutes with every vector, its reverse is `-ω`, and its square is the
scalar `-(Q v₁ ⋯ Q v₆)`. Hence `x = a + b • ω` is an even unit with
`reverse x * x = a² + b² ∏ Q vᵢ`, so `x ∈ U(C₀, σ)` as soon as `a² + b² ∏ Q vᵢ = 1`. Twisted
conjugation by `x` sends a basis vector `v` to `(a² - b² ∏ Q vᵢ) • v + 2ab • ω v`, and `ω v` is not
a vector: any anisotropic `u ⟂ v` would commute with it, forcing it to be proportional to `u`, and
two orthogonal choices of `u` leave only `0`. Since the Lipschitz group preserves the vectors under
twisted conjugation, `x` is not in it whenever `a b ≠ 0`. Over a field of characteristic zero the
conic `a² + δ b² = 1` always has such a point, so the conclusion holds for every nondegenerate
six-dimensional form.

The witness only uses six orthogonal anisotropic vectors, not a basis, so it lives in the Clifford
algebra of every nondegenerate form of dimension at least six. The same computation is why
dimension two is different: there `ω v` is a multiple of the other basis vector, and indeed the
Spin group fills the even unitary group in dimension two.

The dimension-six identification `Spin(Q) ≅ SU(C₀, σ)` and the strictness `SU ≠ U` are classical;
see M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15, and
H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.

## Main results

* `CliffordAlgebra.prod_map_ι_mul_ι_notMem_range_ι`: the volume element of an orthogonal
  anisotropic list of even length at least three moves each member of the list out of the vectors.
* `CliffordAlgebra.exists_mem_evenUnitaryGroup_coe_eq_algebraMap_add_smul_prod_map_ι`: in
  dimension six, `a + b • ω` is an even unitary unit when `a² + b² ∏ Q vᵢ = 1`.
* `CliffordAlgebra.notMem_lipschitzGroup_of_mem_evenUnitaryGroup_of_coe_eq`: such a unit with
  `a b ≠ 0` is not in the Lipschitz group.
* `CliffordAlgebra.range_spinGroup_toUnits_ne_evenUnitaryGroup_of_six_le_finrank`: over a field
  of characteristic zero, the Spin group of a nondegenerate form of dimension at least six is a
  proper subgroup of the even unitary group.
* `TauCeti.exists_sq_add_sq_mul_eq_one`: the conic `a² + b² δ = 1` has a point with both
  coordinates nonzero over every field of characteristic zero.
-/

public section

open Module

namespace TauCeti

/-- **The conic `a² + b² δ = 1` has a point with both coordinates nonzero over every field of
characteristic zero.** The rational parametrisation `t ↦ ((1 - δt²)/(1 + δt²), 2t/(1 + δt²))` at
`t = 1` works unless `δ = ±1`, and those two conics carry the points `(3/5, 4/5)` and
`(5/4, 3/4)`. -/
theorem exists_sq_add_sq_mul_eq_one {K : Type*} [Field K] [CharZero K] (δ : K) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 2 + b ^ 2 * δ = 1 := by
  by_cases h₁ : δ = 1
  · exact ⟨3 / 5, 4 / 5, by norm_num, by norm_num, by rw [h₁]; norm_num⟩
  by_cases h₂ : δ = -1
  · exact ⟨5 / 4, 3 / 4, by norm_num, by norm_num, by rw [h₂]; norm_num⟩
  have h₁' : 1 + δ ≠ 0 := fun h => h₂ (by linear_combination h)
  have h₂' : 1 - δ ≠ 0 := fun h => h₁ (by linear_combination -h)
  refine ⟨(1 - δ) / (1 + δ), 2 / (1 + δ), div_ne_zero h₂' h₁', div_ne_zero two_ne_zero h₁', ?_⟩
  field_simp
  ring

end TauCeti

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-! ### Auxiliary list and volume-element computations -/

/-- Two members of a pairwise orthogonal list of length at least three, orthogonal to a given
member and to each other. The list is split at the given member and the two are its first two
other entries. -/
private theorem exists_isOrtho_pair_of_mem {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (h3 : 3 ≤ l.length) {v : V} (hv : v ∈ l) :
    ∃ u₁ ∈ l, ∃ u₂ ∈ l, Q.IsOrtho v u₁ ∧ Q.IsOrtho v u₂ ∧ Q.IsOrtho u₁ u₂ := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hv
  rw [List.pairwise_append, List.pairwise_cons] at hl
  obtain ⟨hs, ⟨hvt, ht⟩, hst⟩ := hl
  have hortho : ∀ u ∈ s ++ t, Q.IsOrtho v u := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact (hst u hu v List.mem_cons_self).symm
    · exact hvt u hu
  have hpair : (s ++ t).Pairwise Q.IsOrtho :=
    List.pairwise_append.mpr ⟨hs, ht, fun a ha b hb => hst a ha b (List.mem_cons_of_mem v hb)⟩
  have hmem : ∀ u ∈ s ++ t, u ∈ s ++ v :: t := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact List.mem_append_left _ hu
    · exact List.mem_append_right _ (List.mem_cons_of_mem v hu)
  have h0 : 0 < (s ++ t).length := by
    simp only [List.length_append, List.length_cons] at h3 ⊢
    omega
  have h1 : 1 < (s ++ t).length := by
    simp only [List.length_append, List.length_cons] at h3 ⊢
    omega
  exact ⟨(s ++ t)[0], hmem _ (List.getElem_mem h0), (s ++ t)[1], hmem _ (List.getElem_mem h1),
    hortho _ (List.getElem_mem h0), hortho _ (List.getElem_mem h1),
    List.pairwise_iff_getElem.mp hpair 0 1 h0 h1 zero_lt_one⟩

/-- Both products of `a + b • ω` with `a - b • ω`, for `ω` squaring to the scalar `s`. -/
private theorem algebraMap_add_smul_mul_algebraMap_sub_smul {ω : CliffordAlgebra Q} {s : K}
    (hsq : ω * ω = algebraMap K _ s) (a b : K) :
    (algebraMap K _ a + b • ω) * (algebraMap K _ a - b • ω) =
        algebraMap K (CliffordAlgebra Q) (a ^ 2 - b ^ 2 * s) ∧
      (algebraMap K _ a - b • ω) * (algebraMap K _ a + b • ω) =
        algebraMap K (CliffordAlgebra Q) (a ^ 2 - b ^ 2 * s) := by
  constructor <;>
  · simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, sub_mul, mul_sub,
      smul_mul_smul_comm, one_mul, mul_one, hsq, smul_smul]
    module

/-- Twisted conjugation of a vector by `a + b • ω`, for `ω` anticommuting with the vector and
squaring to the scalar `s`. -/
private theorem algebraMap_add_smul_mul_ι_mul_algebraMap_sub_smul {ω : CliffordAlgebra Q} {s : K}
    (hsq : ω * ω = algebraMap K _ s) {v : V} (hv : ω * ι Q v = -(ι Q v * ω)) (a b : K) :
    (algebraMap K _ a + b • ω) * ι Q v * (algebraMap K _ a - b • ω) =
      (a ^ 2 + b ^ 2 * s) • ι Q v + (2 * a * b) • (ω * ι Q v) := by
  have hvω : ι Q v * ω = -(ω * ι Q v) := by rw [hv, neg_neg]
  have h1 : ι Q v * (algebraMap K _ a - b • ω) = (algebraMap K _ a + b • ω) * ι Q v := by
    rw [mul_sub, add_mul, ← Algebra.commutes, mul_smul_comm, smul_mul_assoc, hvω, smul_neg,
      sub_neg_eq_add]
  rw [mul_assoc, h1, ← mul_assoc]
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hsq, smul_smul]
  module

variable {l : List V}

/-- The volume element of an orthogonal list of length six squares to `-∏ Q vᵢ`. -/
private theorem prod_map_ι_sq_of_length_eq_six (hl : l.Pairwise Q.IsOrtho)
    (hlen : l.length = 6) :
    (l.map (ι Q)).prod * (l.map (ι Q)).prod = algebraMap K _ (-(l.map Q).prod) := by
  rw [prod_map_ι_sq_scalar hl, hlen, (by decide : Nat.choose 6 2 = 15),
    Odd.neg_one_pow (by decide : Odd 15), neg_one_mul]

/-- The volume element of an orthogonal list of length six is reverse-antisymmetric. -/
private theorem reverse_prod_map_ι_of_length_eq_six (hl : l.Pairwise Q.IsOrtho)
    (hlen : l.length = 6) : reverse (l.map (ι Q)).prod = -(l.map (ι Q)).prod := by
  rw [reverse_prod_map_ι_of_pairwise_isOrtho hl, hlen, (by decide : Nat.choose 6 2 = 15),
    Odd.neg_one_pow (by decide : Odd 15), neg_one_smul]

/-! ### The witness `a + b • ω` in dimension six -/

/-- **The even unitary units `a + b • ω` in dimension six.** For `ω` the volume element of an
orthogonal anisotropic list of length six, `ω` is even, `reverse ω = -ω` and `ω² = -∏ Q vᵢ`, so
`a + b • ω` is an even unit of reverse norm `a² + b² ∏ Q vᵢ`. When that norm is `1` it lies in the
even unitary group. -/
theorem exists_mem_evenUnitaryGroup_coe_eq_algebraMap_add_smul_prod_map_ι
    (hl : l.Pairwise Q.IsOrtho) (hlen : l.length = 6) {a b : K}
    (hab : a ^ 2 + b ^ 2 * (l.map Q).prod = 1) :
    ∃ x : (CliffordAlgebra Q)ˣ, x ∈ evenUnitaryGroup Q ∧
      (x : CliffordAlgebra Q) = algebraMap K _ a + b • (l.map (ι Q)).prod := by
  obtain ⟨h₁, h₂⟩ := algebraMap_add_smul_mul_algebraMap_sub_smul
    (prod_map_ι_sq_of_length_eq_six hl hlen) a b
  have hnorm : a ^ 2 - b ^ 2 * -(l.map Q).prod = 1 := by rw [← hab]; ring
  rw [hnorm, map_one] at h₁ h₂
  refine ⟨⟨algebraMap K _ a + b • (l.map (ι Q)).prod, algebraMap K _ a - b • (l.map (ι Q)).prod,
    h₁, h₂⟩, ?_, rfl⟩
  rw [evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one, Units.val_mk]
  refine ⟨?_, ?_⟩
  · have hω : (l.map (ι Q)).prod ∈ even Q := by
      have h := prod_map_ι_mem_evenOdd (Q := Q) l
      rw [hlen, (by decide : ((6 : ℕ) : ZMod 2) = 0)] at h
      rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    exact (even Q).add_mem ((even Q).algebraMap_mem a) ((even Q).smul_mem hω b)
  · rw [map_add, map_smul, reverse.commutes, reverse_prod_map_ι_of_length_eq_six hl hlen,
      smul_neg, ← sub_eq_add_neg, h₂]

section Invertible

variable [Invertible (2 : K)]

/-! ### An anticommuting element moves an anisotropic vector out of the vectors -/

/-- **A nonzero element anticommuting with two orthogonal anisotropic companions of an anisotropic
vector `v` sends `ι Q v` outside the vectors.** If `ω * ι Q v` were a vector `ι Q w`, each
companion `u` would commute with it, since `u` anticommutes with both `ω` and `ι Q v`, so `w` would
be proportional to `u` (`CliffordAlgebra.commute_ι_iff_exists_eq_smul`); two orthogonal
anisotropic companions then force `w = 0`, and `ω * ι Q v * ι Q v = Q v • ω` forces `ω = 0`. -/
theorem mul_ι_notMem_range_ι_of_mul_ι_eq_neg {ω : CliffordAlgebra Q} (hω : ω ≠ 0) {v u₁ u₂ : V}
    (hv : Q v ≠ 0) (hu₁ : Q u₁ ≠ 0) (hu₂ : Q u₂ ≠ 0) (hvu₁ : Q.IsOrtho v u₁)
    (hvu₂ : Q.IsOrtho v u₂) (hu₁u₂ : Q.IsOrtho u₁ u₂) (h₁ : ω * ι Q u₁ = -(ι Q u₁ * ω))
    (h₂ : ω * ι Q u₂ = -(ι Q u₂ * ω)) : ω * ι Q v ∉ LinearMap.range (ι Q) := by
  rintro ⟨w, hw⟩
  -- A companion `u` of `v` commutes with `ω * ι Q v`, so `w` is proportional to `u`.
  have key : ∀ u : V, Q u ≠ 0 → Q.IsOrtho v u → ω * ι Q u = -(ι Q u * ω) → ∃ c : K, w = c • u := by
    intro u hu huv hωu
    refine (commute_ι_iff_exists_eq_smul Q (isUnit_iff_ne_zero.mpr hu)).mp ?_
    have hvu : ι Q u * ι Q v = -(ι Q v * ι Q u) := ι_mul_ι_comm_of_isOrtho huv.symm
    have huω : ι Q u * ω = -(ω * ι Q u) := by rw [hωu, neg_neg]
    have : ι Q u * (ω * ι Q v) = ω * ι Q v * ι Q u := by
      calc ι Q u * (ω * ι Q v) = -(ω * ι Q u) * ι Q v := by rw [← mul_assoc, huω]
        _ = -(ω * (ι Q u * ι Q v)) := by rw [neg_mul, mul_assoc]
        _ = ω * ι Q v * ι Q u := by rw [hvu, mul_neg, neg_neg, mul_assoc]
    rw [hw]
    exact this
  obtain ⟨c₁, hc₁⟩ := key u₁ hu₁ hvu₁ h₁
  obtain ⟨c₂, hc₂⟩ := key u₂ hu₂ hvu₂ h₂
  -- Pairing `w` with `u₁` in the two expressions gives `2 c₁ Q u₁ = polar Q u₁ w = 0`.
  have hpolar₁ : QuadraticMap.polar Q u₁ w = c₁ * (2 * Q u₁) := by
    rw [hc₁, QuadraticMap.polar_smul_right, QuadraticMap.polar_self, two_nsmul, smul_eq_mul,
      two_mul]
  have hpolar₂ : QuadraticMap.polar Q u₁ w = 0 := by
    rw [hc₂, QuadraticMap.polar_smul_right, hu₁u₂.polar_eq_zero, smul_zero]
  have hc₁0 : c₁ = 0 := by
    rcases mul_eq_zero.mp (hpolar₁.symm.trans hpolar₂) with h | h
    · exact h
    · exact absurd h (mul_ne_zero (Invertible.ne_zero (2 : K)) hu₁)
  -- So `ω * ι Q v = 0`; multiplying by `ι Q v` once more gives `Q v • ω = 0`.
  have hωv : ω * ι Q v = 0 := by rw [← hw, hc₁, hc₁0, zero_smul, map_zero]
  have hQω : Q v • ω = 0 := by
    rw [Algebra.smul_def, Algebra.commutes, ← ι_sq_scalar, ← mul_assoc, hωv, zero_mul]
  exact hω ((smul_eq_zero.mp hQω).resolve_left hv)

/-- **The volume element of an orthogonal anisotropic list of even length at least three moves each
member of the list out of the vectors.** The volume element anticommutes with every member
(`CliffordAlgebra.prod_map_ι_mul_ι_of_even_length`), is a unit
(`CliffordAlgebra.isUnit_prod_map_ι`), and every member has two orthogonal anisotropic companions
in the list, so `CliffordAlgebra.mul_ι_notMem_range_ι_of_mul_ι_eq_neg` applies. Length two is
genuinely excluded: there the volume element sends each member to a multiple of the other. -/
theorem prod_map_ι_mul_ι_notMem_range_ι {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Even l.length) (h3 : 3 ≤ l.length) (haniso : ∀ v ∈ l, Q v ≠ 0) {v : V}
    (hv : v ∈ l) : (l.map (ι Q)).prod * ι Q v ∉ LinearMap.range (ι Q) := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hvu₁, hvu₂, hu₁u₂⟩ := exists_isOrtho_pair_of_mem hl h3 hv
  have hunit : IsUnit ((l.map Q).prod) :=
    List.prod_isUnit fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact isUnit_iff_ne_zero.mpr (haniso m hm)
  exact mul_ι_notMem_range_ι_of_mul_ι_eq_neg (isUnit_prod_map_ι hunit).ne_zero (haniso v hv)
    (haniso u₁ hu₁) (haniso u₂ hu₂) hvu₁ hvu₂ hu₁u₂
    (prod_map_ι_mul_ι_of_even_length hl hlen (Submodule.subset_span hu₁))
    (prod_map_ι_mul_ι_of_even_length hl hlen (Submodule.subset_span hu₂))

/-! ### The witness is not in the Lipschitz group -/

/-- **An even unitary unit `a + b • ω` with `a b ≠ 0` is not in the Lipschitz group**, for `ω` the
volume element of an orthogonal anisotropic list of length six. Twisted conjugation by it sends a
member `v` of the list to `(a² + b² ω²) • v + 2ab • ω v`, and `ω v` is not a vector
(`CliffordAlgebra.prod_map_ι_mul_ι_notMem_range_ι`), whereas the Lipschitz group preserves the
vectors (`CliffordAlgebra.lipschitzGroup.involute_act_ι_mem_range_ι`). The list need not span:
the witness lives in the Clifford algebra of any quadratic space containing six orthogonal
anisotropic vectors. -/
theorem notMem_lipschitzGroup_of_mem_evenUnitaryGroup_of_coe_eq (hl : l.Pairwise Q.IsOrtho)
    (hlen : l.length = 6) (haniso : ∀ v ∈ l, Q v ≠ 0) {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ evenUnitaryGroup Q)
    {a b : K} (hcoe : (x : CliffordAlgebra Q) = algebraMap K _ a + b • (l.map (ι Q)).prod)
    (ha : a ≠ 0) (hb : b ≠ 0) : x ∉ lipschitzGroup Q := by
  intro hxL
  obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos (l := l) (by omega)
  have heven : Even l.length := by rw [hlen]; exact ⟨3, rfl⟩
  -- `x` is even, so its involute is itself, and its inverse is its reverse `a - b • ω`.
  have hinvol : involute (x : CliffordAlgebra Q) = x := by
    rw [hcoe, map_add, map_smul, involute.commutes, involute_prod_map_ι, hlen,
      Even.neg_one_pow (by decide : Even 6), one_smul]
  have hinv : ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap K _ a - b • (l.map (ι Q)).prod := by
    have h := evenUnitaryGroup.reverse_eq_inv Q ⟨x, hx⟩
    dsimp only at h
    rw [← h, hcoe, map_add, map_smul, reverse.commutes, reverse_prod_map_ι_of_length_eq_six hl hlen,
      smul_neg, ← sub_eq_add_neg]
  have hmem := lipschitzGroup.involute_act_ι_mem_range_ι hxL v
  rw [hinvol, hinv, hcoe, algebraMap_add_smul_mul_ι_mul_algebraMap_sub_smul
    (prod_map_ι_sq_of_length_eq_six hl hlen)
    (prod_map_ι_mul_ι_of_even_length hl heven (Submodule.subset_span hv))] at hmem
  have hsub : (2 * a * b) • ((l.map (ι Q)).prod * ι Q v) ∈ LinearMap.range (ι Q) := by
    have h := (LinearMap.range (ι Q)).sub_mem hmem
      (Submodule.smul_mem _ (a ^ 2 + b ^ 2 * -(l.map Q).prod) (LinearMap.mem_range_self (ι Q) v))
    rwa [add_sub_cancel_left] at h
  exact prod_map_ι_mul_ι_notMem_range_ι hl heven (by omega) haniso hv
    ((Submodule.smul_mem_iff _ (mul_ne_zero (mul_ne_zero (Invertible.ne_zero (2 : K)) ha) hb)).mp
      hsub)

/-- **Given six orthogonal anisotropic vectors, the even unitary group is not contained in the
Lipschitz group** as soon as `a² + b² ∏ Q vᵢ = 1` has a solution with `a b ≠ 0`, the witness being
`a + b • ω` for `ω` their volume element. -/
theorem not_evenUnitaryGroup_le_lipschitzGroup_of_sq_add_sq_mul_eq_one (hl : l.Pairwise Q.IsOrtho)
    (hlen : l.length = 6) (haniso : ∀ v ∈ l, Q v ≠ 0) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ^ 2 + b ^ 2 * (l.map Q).prod = 1) : ¬ evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  intro hle
  obtain ⟨x, hx, hcoe⟩ :=
    exists_mem_evenUnitaryGroup_coe_eq_algebraMap_add_smul_prod_map_ι hl hlen hab
  exact notMem_lipschitzGroup_of_mem_evenUnitaryGroup_of_coe_eq hl hlen haniso hx hcoe ha hb
    (hle hx)

end Invertible

/-! ### Characteristic zero: every nondegenerate form of dimension at least six -/

section CharZero

variable [CharZero K] (Q : QuadraticForm K V)

/-- **Over a field of characteristic zero, the even unitary group of a nondegenerate quadratic form
of dimension at least six is not contained in the Lipschitz group.** Six members of an orthogonal
anisotropic basis have `∏ Q vᵢ = δ`, the conic `a² + b² δ = 1` has a point with `a b ≠ 0`
(`TauCeti.exists_sq_add_sq_mul_eq_one`), and `a + b • ω` is the witness, `ω` their volume
element. -/
theorem not_evenUnitaryGroup_le_lipschitzGroup_of_six_le_finrank (hQ : Q.Nondegenerate)
    (hV : 6 ≤ finrank K V) : ¬ evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨l, hl, hlen, -, haniso⟩ := hQ.exists_list_pairwise_isOrtho
  have hl' : (l.take 6).Pairwise Q.IsOrtho := hl.sublist (List.take_sublist 6 l)
  have hlen' : (l.take 6).length = 6 := by rw [List.length_take]; omega
  obtain ⟨a, b, ha, hb, hab⟩ := TauCeti.exists_sq_add_sq_mul_eq_one ((l.take 6).map Q).prod
  exact not_evenUnitaryGroup_le_lipschitzGroup_of_sq_add_sq_mul_eq_one hl' hlen'
    (fun v hv => haniso v (List.mem_of_mem_take hv)) ha hb hab

/-- **Over a field of characteristic zero, the Spin group of a nondegenerate quadratic form of
dimension at least six is a proper subgroup of the even unitary group inside Clifford units.**
This is where the low-rank identification of Spin with the even unitary group stops. -/
theorem range_spinGroup_toUnits_ne_evenUnitaryGroup_of_six_le_finrank (hQ : Q.Nondegenerate)
    (hV : 6 ≤ finrank K V) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range ≠ evenUnitaryGroup Q := by
  intro h
  refine not_evenUnitaryGroup_le_lipschitzGroup_of_six_le_finrank Q hQ hV ?_
  rw [← h, range_spinGroup_toUnits]
  exact inf_le_left

end CharZero

end CliffordAlgebra
