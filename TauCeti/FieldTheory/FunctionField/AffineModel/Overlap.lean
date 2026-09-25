/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
public import TauCeti.RingTheory.Localization.AsSubring

/-!
# The overlap of the two affine charts of a function field

Let `F / k` be an algebraic function field and `x ∈ F` transcendental over `k`. The affine model
`R_x`, the integral closure of `k[x]` in `F`, is the holomorphy ring of the places at which `x` is
regular (`TauCeti.restrictScalars_integralClosure_adjoin_eq_holomorphyRing`), and the model
`R_{x⁻¹}` is the holomorphy ring of the places at which `x` has no zero. The two charts cover the
place set, since no place is both a zero and a pole of `x`, and they overlap on the places at which
`x` is a unit.

This file identifies the ring of the overlap. Inverting `x` in `R_x` gives the localization
`R_x[1/x]`, realized inside `F` by Mathlib's `Localization.subalgebra.ofField`, and this
localization is the holomorphy ring of the overlap. Applied to `x⁻¹`, the same statement identifies
`R_{x⁻¹}[x]` with the same ring, so the two localizations are one and the same subring of `F`: the
two charts glue along their common localization. The overlap ring is a Dedekind domain whose height
one primes are the places of the overlap, and the prime of the overlap ring below such a place
contracts to the prime of `R_x` below it (`TauCeti.Place.comap_center_asIdeal`).

The identification is proved for an arbitrary holomorphy ring `𝒪_S` and any nonzero `x ∈ 𝒪_S`:
`𝒪_S[1/x]` is the holomorphy ring of the places of `S` at which `x⁻¹` is regular. A function
regular at those places has its poles on `S` only among the finitely many zeros of `x`, so a
sufficiently high power of `x` clears them.

## Main results

* `TauCeti.coe_ofField_powers_eq_holomorphyRing`: if a subalgebra `A` of `F` is the holomorphy ring
  of a set `S` of places and `x ∈ A`, then the localization `A[1/x] ⊆ F` is the holomorphy ring of
  the places of `S` at which `x⁻¹` is regular; `TauCeti.mem_ofField_powers_iff_forall_mem_integers`
  is the membership form.
* `TauCeti.forall_algebraMap_mem_integers_ofField_powers_iff`: the finite chart of `A[1/x]` is the
  set of places of `S` at which `x⁻¹` is regular.
* `TauCeti.ofFieldPowersHeightOneSpectrumEquiv`: for a Dedekind `A`, the places of that chart are
  the height one primes of `A[1/x]`.
* `TauCeti.coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing` and
  `TauCeti.coe_ofField_powers_integralClosure_adjoin_eq_coe_ofField_powers_inv`: the two charts
  `R_x` and `R_{x⁻¹}` localize to one and the same subring of `F`, the holomorphy ring of the
  places at which `x` is a unit.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2.
-/

public section

open IsDedekindDomain Localization.subalgebra

open scoped nonZeroDivisors

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-! ### Clearing poles by a power of a function -/

/-- A function regular at every place of `S` at which `x⁻¹` is regular is made regular on all of
`S` by a sufficiently high power of `x ∈ 𝒪_S`: its poles on `S` are among the finitely many zeros
of `x`. -/
theorem exists_pow_mul_mem_holomorphyRing (hF : IsFunctionField k F) {S : Set (Place k F)}
    {x : F} (hx : x ∈ holomorphyRing S) {z : F}
    (hz : ∀ P ∈ S, x⁻¹ ∈ P.integers → z ∈ P.integers) :
    ∃ n : ℕ, x ^ n * z ∈ holomorphyRing S := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simpa using fun P hP ↦ hz P hP (by simp)⟩
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨0, by simp⟩
  classical
  have hT : {P : Place k F | P.ord z < 0}.Finite := Place.finite_setOf_ord_neg hF z
  set n : ℕ := hT.toFinset.sup fun P ↦ (-P.ord z).toNat with hn
  refine ⟨n, mem_holomorphyRing_iff_forall_ord_nonneg.mpr fun P hP ↦ ?_⟩
  have hxP : 0 ≤ P.ord x := mem_holomorphyRing_iff_forall_ord_nonneg.mp hx P hP
  rw [P.ord_mul (pow_ne_zero n hx0) hz0, P.ord_pow]
  rcases le_or_gt 0 (P.ord z) with hzP | hzP
  · exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) hxP) hzP
  -- `P` is a pole of `z`, hence a zero of `x`, and `n` was chosen to absorb it.
  have hxpos : 0 < P.ord x := by
    by_contra h
    have hxinv : x⁻¹ ∈ P.integers := by
      rw [P.mem_integers_iff_ord_nonneg, P.ord_inv]
      omega
    have := P.mem_integers_iff_ord_nonneg.mp (hz P hP hxinv)
    omega
  have hle : (-P.ord z).toNat ≤ n :=
    Finset.le_sup (f := fun P : Place k F ↦ (-P.ord z).toNat) (hT.mem_toFinset.mpr hzP)
  have h1 : ((-P.ord z).toNat : ℤ) = -P.ord z := Int.toNat_of_nonneg (by omega)
  have h2 : ((-P.ord z).toNat : ℤ) ≤ n := by exact_mod_cast hle
  have h3 : (n : ℤ) ≤ n * P.ord x := le_mul_of_one_le_right (Nat.cast_nonneg n) hxpos
  linarith

/-! ### The localization of a holomorphy ring away from a function -/

section Localization

variable {R : Type*} [CommRing R] [Algebra R F] {A : Subalgebra R F} [IsFractionRing A F]
  {S : Set (Place k F)}

/-- **`𝒪_S[1/x]` is the holomorphy ring of the places of `S` at which `x⁻¹` is regular.** Stated
for a subalgebra `A` of `F` that is, as a set, the holomorphy ring of `S`, so that it applies to the
affine model `R_x` as well as to `𝒪_S` itself. -/
theorem coe_ofField_powers_eq_holomorphyRing (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰) :
    (ofField F (Submonoid.powers x) hx : Set F) =
      holomorphyRing (S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers}) := by
  have hA' : ∀ y : F, y ∈ A ↔ y ∈ holomorphyRing S := fun y ↦ by
    rw [← SetLike.mem_coe, hA, SetLike.mem_coe]
  have hx0 : (x : F) ≠ 0 := fun h ↦
    nonZeroDivisors.ne_zero (hx (Submonoid.mem_powers x)) (Subtype.ext h)
  ext z
  rw [SetLike.mem_coe, mem_ofField_powers_iff, Subalgebra.range_algebraMap, SetLike.mem_coe,
    mem_holomorphyRing_iff]
  simp only [Subalgebra.mem_toSubring, Subalgebra.algebraMap_apply, hA', mem_holomorphyRing_iff,
    Set.mem_inter_iff, Set.mem_ofPred_eq, and_imp]
  constructor
  · rintro ⟨n, hn⟩ P hP hPx
    have hz : z = (x : F)⁻¹ ^ n * ((x : F) ^ n * z) := by
      rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero n hx0), one_mul]
    rw [hz]
    exact mul_mem (pow_mem hPx n) (hn P hP)
  · intro h
    obtain ⟨n, hn⟩ :=
      exists_pow_mul_mem_holomorphyRing hF ((hA' x).mp x.2) fun P hP hPx ↦ h P hP hPx
    exact ⟨n, mem_holomorphyRing_iff.mp hn⟩

/-- **Membership in `𝒪_S[1/x]`**: a function lies in the localization exactly when it is regular
at every place of `S` at which `x⁻¹` is regular. -/
theorem mem_ofField_powers_iff_forall_mem_integers (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    {z : F} :
    z ∈ ofField F (Submonoid.powers x) hx ↔
      ∀ P ∈ S, (x : F)⁻¹ ∈ P.integers → z ∈ P.integers := by
  rw [← SetLike.mem_coe, coe_ofField_powers_eq_holomorphyRing hF hA x hx, SetLike.mem_coe,
    mem_holomorphyRing_iff]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_imp]

/-- **The finite chart of `𝒪_S[1/x]`**: a place is finite on the localization exactly when it
belongs to `S` and `x⁻¹` is regular there. -/
theorem forall_algebraMap_mem_integers_ofField_powers_iff (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    {P : Place k F} :
    (∀ a : ofField F (Submonoid.powers x) hx, algebraMap _ F a ∈ P.integers) ↔
      P ∈ S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers} := by
  rw [← coe_holomorphyRing_subset_integers_iff hF,
    ← coe_ofField_powers_eq_holomorphyRing hF hA x hx]
  exact ⟨fun h a ha ↦ h ⟨a, ha⟩, fun h a ↦ h a.2⟩

variable [Algebra k A] [IsScalarTower k A F] [IsDedekindDomain A]

/-- **The height one primes of `𝒪_S[1/x]` are the places of `S` at which `x⁻¹` is regular**, for
a Dedekind `𝒪_S`: `TauCeti.Place.heightOneSpectrumEquiv` for the localization, read along the
identification of its finite chart. -/
noncomputable def ofFieldPowersHeightOneSpectrumEquiv (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰) :
    ↥(S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers}) ≃
      HeightOneSpectrum (ofField F (Submonoid.powers x) hx) :=
  (Equiv.subtypeEquivRight fun _ ↦
      (forall_algebraMap_mem_integers_ofField_powers_iff hF hA x hx).symm).trans
    (Place.heightOneSpectrumEquiv k F _)

@[simp]
theorem ofFieldPowersHeightOneSpectrumEquiv_apply (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    (P : ↥(S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers})) :
    ofFieldPowersHeightOneSpectrumEquiv hF hA x hx P =
      (P : Place k F).center
        ((forall_algebraMap_mem_integers_ofField_powers_iff hF hA x hx).mpr P.2) :=
  Place.heightOneSpectrumEquiv_apply k F _

@[simp]
theorem coe_ofFieldPowersHeightOneSpectrumEquiv_symm_apply (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    (𝔭 : HeightOneSpectrum (ofField F (Submonoid.powers x) hx)) :
    ((ofFieldPowersHeightOneSpectrumEquiv hF hA x hx).symm 𝔭 : Place k F) =
      Place.ofPrime k F 𝔭 :=
  Place.coe_heightOneSpectrumEquiv_symm_apply k F 𝔭

end Localization

/-! ### The two charts `R_x` and `R_{x⁻¹}` glue along their common localization -/

section IntegralClosureAdjoin

variable (x : F)

/-- `x` lies in its own affine model `R_x`, the integral closure of `k[x]` in `F`. -/
theorem self_mem_integralClosure_adjoin : x ∈ integralClosure (Algebra.adjoin k {x}) F :=
  isIntegral_algebraMap (x := (⟨x, Algebra.self_mem_adjoin_singleton k x⟩ : Algebra.adjoin k {x}))

variable [IsFractionRing (integralClosure (Algebra.adjoin k {x}) F) F]

/-- **`R_x[1/x]` is the holomorphy ring of the overlap of the two charts**: the places at which
`x` is a unit, the intersection of the finite chart of `R_x` with that of `R_{x⁻¹}`. -/
theorem coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing (hF : IsFunctionField k F)
    (hx : Submonoid.powers
      (⟨x, self_mem_integralClosure_adjoin x⟩ : integralClosure (Algebra.adjoin k {x}) F) ≤
        (integralClosure (Algebra.adjoin k {x}) F)⁰) :
    (ofField F (Submonoid.powers
      (⟨x, self_mem_integralClosure_adjoin x⟩ : integralClosure (Algebra.adjoin k {x}) F)) hx :
        Set F) =
      holomorphyRing ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers}) :=
  coe_ofField_powers_eq_holomorphyRing hF (by
    rw [← Subalgebra.coe_restrictScalars k,
      restrictScalars_integralClosure_adjoin_eq_holomorphyRing hF]) _ hx

/-- **The two charts glue along their common localization**: inside `F`, the localization
`R_x[1/x]` of the model of `x` and the localization `R_{x⁻¹}[x]` of the model of `x⁻¹` are one
and the same subring, the holomorphy ring of the places at which `x` is a unit. -/
theorem coe_ofField_powers_integralClosure_adjoin_eq_coe_ofField_powers_inv
    (hF : IsFunctionField k F)
    [IsFractionRing (integralClosure (Algebra.adjoin k {x⁻¹}) F) F]
    (hx : Submonoid.powers
      (⟨x, self_mem_integralClosure_adjoin x⟩ : integralClosure (Algebra.adjoin k {x}) F) ≤
        (integralClosure (Algebra.adjoin k {x}) F)⁰)
    (hx' : Submonoid.powers
      (⟨x⁻¹, self_mem_integralClosure_adjoin x⁻¹⟩ : integralClosure (Algebra.adjoin k {x⁻¹}) F) ≤
        (integralClosure (Algebra.adjoin k {x⁻¹}) F)⁰) :
    (ofField F (Submonoid.powers
      (⟨x, self_mem_integralClosure_adjoin x⟩ : integralClosure (Algebra.adjoin k {x}) F)) hx :
        Set F) =
      (ofField F (Submonoid.powers
        (⟨x⁻¹, self_mem_integralClosure_adjoin x⁻¹⟩ :
          integralClosure (Algebra.adjoin k {x⁻¹}) F)) hx' : Set F) := by
  rw [coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing x hF hx,
    coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing x⁻¹ hF hx', inv_inv,
    Set.inter_comm]

end IntegralClosureAdjoin

end TauCeti
