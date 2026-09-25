/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.NumberTheory.Padics.PrincipalUnits
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Henselian.Teichmuller
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# The Teichmüller splitting of `ℤ_pˣ` and the pro-`p` subgroups of `ℤ_pˣ`

The unit group of the `p`-adic integers splits as the direct product of the group `μ_{p-1}` of
`(p - 1)`-st roots of unity and the principal unit group `1 + pℤ_p`:

`ℤ_pˣ ≃ₜ* μ_{p-1} × (1 + pℤ_p)`,

where a unit `u` goes to the Teichmüller representative of its residue class modulo `p`, the
unique root of unity congruent to `u` modulo `p`, together with `u` divided by it, and where the
inverse is multiplication. This is the Teichmüller splitting of the Henselian local ring `ℤ_p`
(`TauCeti.unitsMulEquivRootsOfUnityProdKerResidue`), whose residue field is `ℤ/pℤ`, so that the
kernel of reduction on units is the principal unit group `TauCeti.unitsPrincipal p 1`; the
inverse multiplication map is continuous, and `ℤ_pˣ` is compact, so the splitting is a
topological isomorphism. The first factor `μ_{p-1}` is cyclic of order `p - 1`.

The prime-to-`p` factor `μ_{p-1}` is what keeps a subgroup of `ℤ_pˣ` from being pro-`p`: the
pro-`p` subgroups of `ℤ_pˣ` are exactly the subgroups of `1 + pℤ_p`. Every principal unit group
`1 + p^f ℤ_p` with `f ≥ 1` is pro-`p`, because its finite quotients `U^(f) / U^(f+k)` have order
`p ^ k`, and a pro-`p` subgroup has trivial image in the quotient `ℤ_pˣ / (1 + pℤ_p)` of order
`p - 1`. For `p = 2` the principal unit group `1 + 2ℤ_2` is all of `ℤ_2ˣ`, so every subgroup of
`ℤ_2ˣ` is pro-`2`.

## Main declarations

* `TauCeti.isComplement'_rootsOfUnity_unitsPrincipal_one`: `μ_{p-1}` and `1 + pℤ_p` are
  complementary subgroups of `ℤ_pˣ`.
* `TauCeti.padicIntUnitsEquivProd`: the Teichmüller splitting `ℤ_pˣ ≃ₜ* μ_{p-1} × (1 + pℤ_p)`,
  with `TauCeti.padicIntUnitsEquivProd_symm_apply`,
  `TauCeti.toZMod_padicIntUnitsEquivProd_apply_fst` and
  `TauCeti.coe_padicIntUnitsEquivProd_apply_snd` describing its two components.
* `TauCeti.card_rootsOfUnity_padicInt`: `μ_{p-1}` has `p - 1` elements.
* `TauCeti.isProP_unitsPrincipal`: `1 + p^f ℤ_p` is pro-`p` for `f ≥ 1`.
* `TauCeti.IsProP.le_unitsPrincipal_one`, `TauCeti.isProP_iff_le_unitsPrincipal_one`: a subgroup
  of `ℤ_pˣ` is pro-`p` exactly when it lies in `1 + pℤ_p`.
* `TauCeti.isProP_two_subgroup_units`: every subgroup of `ℤ_2ˣ` is pro-`2`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition 5.3 and Proposition 5.7.
* J.-P. Serre, *Corps Locaux*, Chapter II, §4.
* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), the remark
  following the corollary to Theorem 4.
-/

public section

open IsLocalRing

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The Teichmüller splitting -/

variable (p) in
/-- The principal unit group `1 + pℤ_p` is the kernel of reduction on units. -/
theorem unitsPrincipal_one_eq_ker_unitsMap_residue :
    unitsPrincipal p 1 = (Units.map (residue ℤ_[p] : ℤ_[p] →* ResidueField ℤ_[p])).ker := by
  ext u
  rw [mem_unitsPrincipal_one_iff_residue, MonoidHom.mem_ker, Units.ext_iff]
  simp

variable (p) in
/-- **The Teichmüller splitting of `ℤ_pˣ`, as complementary subgroups**: every unit of `ℤ_p` is
uniquely the product of a `(p - 1)`-st root of unity and a principal unit. -/
theorem isComplement'_rootsOfUnity_unitsPrincipal_one :
    (rootsOfUnity (p - 1) ℤ_[p]).IsComplement' (unitsPrincipal p 1) := by
  have h := isComplement'_rootsOfUnity_ker_unitsMap_residue ℤ_[p]
  rwa [PadicInt.card_residueField, ← unitsPrincipal_one_eq_ker_unitsMap_residue] at h

variable (p) in
/-- **The Teichmüller splitting of `ℤ_pˣ`**, `ℤ_pˣ ≃ₜ* μ_{p-1} × (1 + pℤ_p)`: a unit `u` goes to
the unique `(p - 1)`-st root of unity congruent to `u` modulo `p` together with `u` divided by it,
and the inverse is multiplication. -/
noncomputable def padicIntUnitsEquivProd :
    ℤ_[p]ˣ ≃ₜ* rootsOfUnity (p - 1) ℤ_[p] × unitsPrincipal p 1 :=
  have : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  have : CompactSpace (unitsPrincipal p 1) :=
    isCompact_iff_compactSpace.mp (isClosed_unitsPrincipal p 1).isCompact
  let e : rootsOfUnity (p - 1) ℤ_[p] × unitsPrincipal p 1 ≃* ℤ_[p]ˣ :=
    MulEquiv.ofBijective ((rootsOfUnity _ ℤ_[p]).subtype.coprod (unitsPrincipal p 1).subtype)
      ((Subgroup.isComplement_iff_bijective _ _).mp
        (isComplement'_rootsOfUnity_unitsPrincipal_one p))
  -- Multiplication is continuous, and a continuous bijection from a compact space to a Hausdorff
  -- space is a homeomorphism.
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  (ContinuousMulEquiv.mk e he (he.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv))).symm

/-- The inverse of the Teichmüller splitting of `ℤ_pˣ` is multiplication, `(ζ, v) ↦ ζ * v`. -/
@[simp]
theorem padicIntUnitsEquivProd_symm_apply (x : rootsOfUnity (p - 1) ℤ_[p] × unitsPrincipal p 1) :
    (padicIntUnitsEquivProd p).symm x = x.1 * x.2 :=
  (rfl)

/-- The principal-unit component of a unit `u` is `u` divided by its root-of-unity component. -/
@[simp]
theorem coe_padicIntUnitsEquivProd_apply_snd (u : ℤ_[p]ˣ) :
    ((padicIntUnitsEquivProd p u).2 : ℤ_[p]ˣ) =
      ((padicIntUnitsEquivProd p u).1 : ℤ_[p]ˣ)⁻¹ * u := by
  have h := (padicIntUnitsEquivProd p).symm_apply_apply u
  rw [padicIntUnitsEquivProd_symm_apply] at h
  rw [eq_inv_mul_iff_mul_eq, h]

/-- The root-of-unity component of a unit `u` is congruent to `u` modulo `p`. -/
@[simp]
theorem toZMod_padicIntUnitsEquivProd_apply_fst (u : ℤ_[p]ˣ) :
    PadicInt.toZMod (((padicIntUnitsEquivProd p u).1 : ℤ_[p]ˣ) : ℤ_[p]) =
      PadicInt.toZMod (u : ℤ_[p]) := by
  have h := mem_unitsPrincipal_one_iff_toZMod.mp (padicIntUnitsEquivProd p u).2.2
  rw [coe_padicIntUnitsEquivProd_apply_snd, Units.val_mul, map_mul] at h
  have h' : PadicInt.toZMod ((((padicIntUnitsEquivProd p u).1 : ℤ_[p]ˣ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
      PadicInt.toZMod (((padicIntUnitsEquivProd p u).1 : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h) (h'.trans h.symm)

variable (p) in
/-- The group `μ_{p-1}` of `(p - 1)`-st roots of unity of `ℤ_p` has `p - 1` elements. -/
theorem card_rootsOfUnity_padicInt : Nat.card (rootsOfUnity (p - 1) ℤ_[p]) = p - 1 := by
  have h := card_rootsOfUnity ℤ_[p]
  rwa [PadicInt.card_residueField] at h

/-! ### The pro-`p` subgroups of `ℤ_pˣ` -/

variable (p) in
/-- **The principal unit groups are pro-`p`**: for `f ≥ 1`, `1 + p^f ℤ_p` is a pro-`p` group. -/
theorem isProP_unitsPrincipal {f : ℕ} (hf : 0 < f) : IsProP p (unitsPrincipal p f) := by
  rw [Subgroup.isProP_iff_isPGroup_map_mk']
  intro U g
  -- `U` contains a principal unit group `U^(k)`, and `u ^ (p ^ k) ∈ U^(f + k) ≤ U^(k)` for
  -- `u ∈ U^(f)`.
  obtain ⟨k, -, hk⟩ := (hasBasis_nhds_one_unitsPrincipal p).mem_iff.mp
    (U.isOpen.mem_nhds (one_mem _))
  obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hgu, ← map_pow, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact hk (unitsPrincipal_antitone p (Nat.le_add_left k f) (pow_pow_mem_unitsPrincipal hf hu k))

/-- **A pro-`p` subgroup of `ℤ_pˣ` consists of principal units.** Its image in the quotient
`ℤ_pˣ / (1 + pℤ_p)`, a group of order `p - 1`, is a `p`-group, hence trivial. -/
theorem IsProP.le_unitsPrincipal_one {A : Subgroup ℤ_[p]ˣ} (hA : IsProP p A) :
    A ≤ unitsPrincipal p 1 := by
  have hU : IsPGroup p (A.map (QuotientGroup.mk' (unitsPrincipal p 1))) :=
    A.isProP_iff_isPGroup_map_mk'.mp hA
      ⟨⟨unitsPrincipal p 1, isOpen_unitsPrincipal p 1⟩, inferInstance⟩
  have : Finite (ℤ_[p]ˣ ⧸ unitsPrincipal p 1) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_unitsPrincipal p 1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU
  have hidx : Nat.card (ℤ_[p]ˣ ⧸ unitsPrincipal p 1) = p - 1 := by
    rw [← Subgroup.index_eq_card, index_unitsPrincipal_of_pos p one_pos]
    simp
  have hdvd := Subgroup.card_subgroup_dvd_card (A.map (QuotientGroup.mk' (unitsPrincipal p 1)))
  rw [hn, hidx] at hdvd
  have hcop : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right hp.out.one_lt.le).mpr (Nat.coprime_one_right p)
  rw [(hcop.pow_left n).eq_one_of_dvd hdvd, Subgroup.card_eq_one, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hn
  exact hn

/-- **The pro-`p` subgroups of `ℤ_pˣ`** are exactly the subgroups of `1 + pℤ_p`. -/
theorem isProP_iff_le_unitsPrincipal_one (A : Subgroup ℤ_[p]ˣ) :
    IsProP p A ↔ A ≤ unitsPrincipal p 1 :=
  ⟨IsProP.le_unitsPrincipal_one, fun h ↦ (isProP_unitsPrincipal p one_pos).mono h⟩

/-- Every subgroup of `ℤ_2ˣ` is pro-`2`, because `1 + 2ℤ_2 = ℤ_2ˣ`. -/
theorem isProP_two_subgroup_units (A : Subgroup ℤ_[2]ˣ) : IsProP 2 A :=
  (isProP_iff_le_unitsPrincipal_one A).mpr (by rw [unitsPrincipal_two_one]; exact le_top)

end TauCeti
