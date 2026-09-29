/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.ContinuousMonoidHom
import TauCeti.Data.ZMod.Four

/-!
# Lifting characters of `ℤ_p^ι × ℤ_p ⧸ (q)` from `𝔽₂` to `ℤ/4`

An additive homomorphism `ψ : ℤ_p → 𝔽_p` is determined by `ψ 1`: it kills `pℤ_p`, so it is
`x ↦ (x mod p) ψ(1)`. Consequently a continuous character of the abelian pro-`p` group
`A = ℤ_p^ι × ℤ_p ⧸ (q)`, `ι` finite and `p ∣ q`, with values in `𝔽_p` is a combination of the
reductions modulo `p` of the coordinates. At `p = 2` this decides when such a character lifts to a
continuous character with values in `ℤ/4`:

* if `4 ∣ q`, including `q = 0`, every character `A → 𝔽₂` lifts, the lift being the same
  combination of the truncations modulo `4` of the coordinates;
* if `q = 2`, the reduction `(x, y) ↦ y mod 2` on the factor `ℤ_2 ⧸ (2) = 𝔽₂` does not lift: a
  lift would take an element of order two to an element of `ℤ/4` killed by `2`, whose reduction
  modulo `2` is `0`.

This is the module-theoretic side of the fact that the cup square on `H¹(G, 𝔽₂)` of a Demushkin
group `G` vanishes identically exactly when its invariant `q` is not `2`: through
`G^{ab} ≅ ℤ_2^{n-1} × ℤ_2 ⧸ (q)`, the characters of `G` with values in `𝔽₂` that lift to `ℤ/4` are
exactly those with vanishing cup square.

## Main declarations

* `PadicInt.addMonoidHom_apply_eq_toZMod_mul_apply_one`: an additive homomorphism `ℤ_p → 𝔽_p` is
  `x ↦ (x mod p) ψ(1)`.
* `PadicInt.piProdQuotientSpanToZMod`: the character `(x, y) ↦ y mod p` of
  `ℤ_p^ι × ℤ_p ⧸ (q)`, for `p ∣ q`.
* `PadicInt.exists_forall_castHom_toAdd_eq_toAdd_of_pow_two_dvd`: **for `4 ∣ q`, every continuous
  character `ℤ_2^ι × ℤ_2 ⧸ (q) → 𝔽₂` lifts to `ℤ/4`.**
* `PadicInt.exists_castHom_toAdd_ne_toAdd_piProdQuotientSpanToZMod`: **the character
  `(x, y) ↦ y mod 2` of `ℤ_2^ι × ℤ_2 ⧸ (2)` does not lift to `ℤ/4`.**
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **An additive homomorphism `ℤ_p → 𝔽_p` is determined by its value at `1`**: it kills `pℤ_p`,
so it is `x ↦ (x mod p) ψ(1)`. -/
theorem addMonoidHom_apply_eq_toZMod_mul_apply_one (ψ : ℤ_[p] →+ ZMod p) (x : ℤ_[p]) :
    ψ x = toZMod x * ψ 1 := by
  have hmem : x - (ZMod.cast (toZMod x) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← maximalIdeal_eq_span_p]
    exact toZMod_spec x
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [ZMod.cast_eq_val] at ha
  have hx : x = (toZMod x).val • (1 : ℤ_[p]) + p • a := by
    rw [nsmul_one, nsmul_eq_mul]
    linear_combination -ha
  conv_lhs => rw [hx]
  rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_self, zero_mul, add_zero]

variable {ι : Type*} {q : ℤ_[p]}

/-- **The character `(x, y) ↦ y mod p` of `ℤ_p^ι × ℤ_p ⧸ (q)`**, for `p ∣ q`: the reduction
modulo `p` of the second coordinate, as a continuous character with values in `𝔽_p`. -/
noncomputable def piProdQuotientSpanToZMod (hq : (p : ℤ_[p]) ∣ q) :
    Multiplicative ((ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})) →ₜ* Multiplicative (ZMod p) where
  toFun a := Multiplicative.ofAdd (quotientSpanToZMod hq (Multiplicative.toAdd a).2)
  map_one' := by simp
  map_mul' a b := by simp [← ofAdd_add]
  continuous_toFun :=
    continuous_ofAdd.comp
      ((continuous_quotientSpanToZMod hq).comp (continuous_snd.comp continuous_toAdd))

/-- The character `(x, y) ↦ y mod p` takes the value `y mod p` at `(x, y)`. -/
@[simp]
theorem piProdQuotientSpanToZMod_ofAdd (hq : (p : ℤ_[p]) ∣ q) (x : ι → ℤ_[p])
    (y : ℤ_[p] ⧸ Ideal.span {q}) :
    piProdQuotientSpanToZMod hq (Multiplicative.ofAdd (x, y)) =
      Multiplicative.ofAdd (quotientSpanToZMod hq y) :=
  (rfl)

/-! ### Lifting from `𝔽₂` to `ℤ/4` -/

/-- **For `4 ∣ q`, every continuous character `ℤ_2^ι × ℤ_2 ⧸ (q) → 𝔽₂` lifts to `ℤ/4`**: writing
the character as `(x, y) ↦ ∑ᵢ (xᵢ mod 2) cᵢ + (y mod 2) c₀`, the same combination of the
truncations modulo `4` of the coordinates is a continuous character with values in `ℤ/4` whose
reduction modulo `2` is the given one. This includes `q = 0`. -/
theorem exists_forall_castHom_toAdd_eq_toAdd_of_pow_two_dvd [Finite ι] {q : ℤ_[2]}
    (hq : (2 : ℤ_[2]) ^ 2 ∣ q)
    (χ : Multiplicative ((ι → ℤ_[2]) × (ℤ_[2] ⧸ Ideal.span {q})) →ₜ* Multiplicative (ZMod 2)) :
    ∃ φ : Multiplicative ((ι → ℤ_[2]) × (ℤ_[2] ⧸ Ideal.span {q})) →ₜ* Multiplicative (ZMod 4),
      ∀ a, ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ a)) =
        Multiplicative.toAdd (χ a) := by
  classical
  cases nonempty_fintype ι
  set ρ := quotientSpanToZModPow 2 hq with hρ
  -- The additive form of `χ`.
  let χ' : (ι → ℤ_[2]) × (ℤ_[2] ⧸ Ideal.span {q}) →+ ZMod 2 :=
    { toFun := fun a ↦ Multiplicative.toAdd (χ (Multiplicative.ofAdd a))
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [ofAdd_add] }
  -- Its coefficients on the coordinates.
  set c : ι → ZMod 2 := fun i ↦ χ' (Pi.single i 1, 0) with hc
  set c₀ : ZMod 2 := χ' (0, 1) with hc₀
  have hP : ∀ x : ι → ℤ_[2], χ' (x, 0) = ∑ i, toZMod (x i) * c i := by
    intro x
    have h := congrArg (χ'.comp (AddMonoidHom.inl (ι → ℤ_[2]) (ℤ_[2] ⧸ Ideal.span {q})))
      (Finset.univ_sum_single x).symm
    rw [map_sum] at h
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.inl_apply] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simpa [AddMonoidHom.comp_apply] using addMonoidHom_apply_eq_toZMod_mul_apply_one
      (χ'.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single (fun _ ↦ ℤ_[2]) i))) (x i)
  have hQ : ∀ y : ℤ_[2], χ' (0, Ideal.Quotient.mk _ y) = toZMod y * c₀ := fun y ↦ by
    simpa [AddMonoidHom.comp_apply] using addMonoidHom_apply_eq_toZMod_mul_apply_one
      (χ'.comp ((AddMonoidHom.inr _ _).comp (Ideal.Quotient.mk _).toAddMonoidHom)) y
  -- The lift, as an additive homomorphism.
  let φ' : (ι → ℤ_[2]) × (ℤ_[2] ⧸ Ideal.span {q}) →+ ZMod 4 :=
    { toFun := fun a ↦ ∑ i, toZModPow 2 (a.1 i) * (ZMod.cast (c i) : ZMod 4) +
        ρ a.2 * (ZMod.cast c₀ : ZMod 4)
      map_zero' := by simp
      map_add' := fun a b ↦ by
        simp only [Prod.fst_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib,
          Prod.snd_add]
        abel }
  have hφ' : Continuous φ' :=
    (continuous_finsetSum _ fun i _ ↦ (((continuous_toZModPow 2).comp
      ((continuous_apply i).comp continuous_fst)).mul continuous_const)).add
      (((continuous_quotientSpanToZModPow 2 hq).comp continuous_snd).mul continuous_const)
  refine ⟨⟨AddMonoidHom.toMultiplicative φ', continuous_ofAdd.comp (hφ'.comp continuous_toAdd)⟩,
    fun a ↦ ?_⟩
  obtain ⟨⟨x, y⟩, rfl⟩ := Multiplicative.ofAdd.surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hχ : χ' (x, Ideal.Quotient.mk _ y) = ∑ i, toZMod (x i) * c i + toZMod y * c₀ := by
    rw [← hP, ← hQ, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  -- `AddMonoidHom.toMultiplicative` and `toAdd ∘ ofAdd` unfold definitionally, and `χ'` is `χ`
  -- read additively, so both sides are the additive maps evaluated at `(x, y)`.
  change ZMod.castHom _ (ZMod 2) (φ' (x, Ideal.Quotient.mk _ y)) = χ' (x, Ideal.Quotient.mk _ y)
  rw [hχ]
  simp only [φ', AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, map_sum, map_mul,
    ZMod.castHom_apply, ZMod.cast_cast_zmod_of_le (by norm_num : 2 ≤ 4), hρ,
    quotientSpanToZModPow_mk, cast_toZModPow_eq_toZMod two_ne_zero]

/-- **The character `(x, y) ↦ y mod 2` of `ℤ_2^ι × ℤ_2 ⧸ (2)` does not lift to `ℤ/4`**: the
element `(0, 1)` has order two, so a lift would send it to an element of `ℤ/4` killed by `2`, whose
reduction modulo `2` is `0`, while the character takes the value `1` there. -/
theorem exists_castHom_toAdd_ne_toAdd_piProdQuotientSpanToZMod
    (φ : Multiplicative ((ι → ℤ_[2]) × (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])})) →ₜ*
      Multiplicative (ZMod 4)) :
    ∃ a, ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ a)) ≠
      Multiplicative.toAdd (piProdQuotientSpanToZMod (q := (2 : ℤ_[2])) (dvd_refl _) a) := by
  refine ⟨Multiplicative.ofAdd (0, Ideal.Quotient.mk _ 1), fun h ↦ ?_⟩
  rw [piProdQuotientSpanToZMod_ofAdd, quotientSpanToZMod_mk, toAdd_ofAdd, map_one toZMod] at h
  set t : Multiplicative ((ι → ℤ_[2]) × (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])})) :=
    Multiplicative.ofAdd (0, Ideal.Quotient.mk _ 1) with ht
  have hsq : t * t = 1 := by
    rw [← ofAdd_add, Prod.mk_add_mk, add_zero, ← map_add, one_add_one_eq_two,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), ofAdd_eq_one]
    rfl
  have h2 : 2 * Multiplicative.toAdd (φ t) = 0 := by
    rw [two_mul, ← toAdd_mul, ← map_mul, hsq, map_one, toAdd_one]
  rw [ZMod.castHom_eq_zero_of_two_mul_eq_zero h2] at h
  exact zero_ne_one h

end PadicInt
