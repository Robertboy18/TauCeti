/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The slash action on the imaginary axis

The restriction `UpperHalfPlane.resToImagAxis` of a function on `ℍ` to the positive imaginary
axis intertwines the weight-`k` slash action of `S = ![![0, -1], ![1, 0]]` with the involution
`t ↦ 1 / t` of the axis. This is the reflection underlying the functional equation of the
L-function of a modular form, and, in weight `2`, the change of variables that moves the finite
endpoint of a geodesic between cusps to `i∞`.

A cusp form slashed by a rational matrix is a cusp form on the conjugate arithmetic level, so its
restriction to the imaginary axis decays exponentially; this is the convergence input for
integrals of cusp forms along geodesics between cusps.

## Main results

* `UpperHalfPlane.resToImagAxis_slash_S`: the restriction of `F ∣[k] S` at `t` is
  `i ^ (-k) t ^ (-k)` times the restriction of `F` at `1 / t`, and
  `UpperHalfPlane.resToImagAxis_slash_two_S`: in weight `2` this is `-t⁻²` times the restriction
  of `F` at `1 / t`.
* `UpperHalfPlane.resToImagAxis_slash_two_of_diagonal`: in weight `2`, the restriction of
  `F ∣[2] d` for a positive diagonal rational matrix `d = diag(a, b)` at `t` is `r` times the
  restriction of `F` at `r t`, where `r = a / b`.
* `UpperHalfPlane.exists_isBigO_resToImagAxis_rat_slash_exp`: for a cusp form `f` on an
  arithmetic subgroup and `g ∈ GL(2, ℚ)`, the restriction of `f ∣[k] g` to the imaginary axis is
  `O(exp (-c t))` for some `c > 0`.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/ResToImagAxis.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>); the generic
material about the restriction is in
`TauCeti/Analysis/Complex/UpperHalfPlane/ResToImagAxis.lean`.
-/

public section

open Complex ModularGroup

open scoped ModularForm MatrixGroups Pointwise

namespace UpperHalfPlane

/-- **The `S`-involution on the imaginary axis**: slashing by `S` turns `t` into `1 / t`,
`(F ∣[k] S) (i t) = i ^ (-k) t ^ (-k) F (i / t)`. This is the reflection underlying the
functional equation of the L-function. -/
theorem resToImagAxis_slash_S (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis (F ∣[k] S) t =
      Complex.I ^ (-k) * (t : ℂ) ^ (-k) * resToImagAxis F (1 / t) := by
  have ht' : (0 : ℝ) < 1 / t := by positivity
  have h : mk _ (⟨Complex.I * t, by simpa using ht⟩ : ℍ).im_inv_neg_coe_pos =
      (⟨Complex.I * (1 / t : ℝ), by simpa using ht'⟩ : ℍ) :=
    UpperHalfPlane.ext (by
      -- `(-(i t))⁻¹ = i / t`, since `i * i = -1`
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      field_simp
      linear_combination -hI)
  rw [resToImagAxis_of_pos _ ht, SlashInvariantForm.slash_S_apply, h,
    resToImagAxis_of_pos F ht']
  simp only [mul_zpow]
  ring

/-- **The `S`-involution in weight `2`**: `(F ∣[2] S) (i t) = -t⁻² F (i / t)`, the reflection
`t ↦ 1 / t` of the axis together with its Jacobian. -/
theorem resToImagAxis_slash_two_S (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis (F ∣[(2 : ℤ)] S) t = -((t : ℂ) ^ 2)⁻¹ * resToImagAxis F t⁻¹ := by
  rw [resToImagAxis_slash_S F 2 ht, one_div]
  have hI : (Complex.I : ℂ) ^ (-(2 : ℤ)) = -1 := by
    rw [zpow_neg, zpow_two, Complex.I_mul_I]
    norm_num
  rw [hI, zpow_neg, zpow_two, sq]
  ring

/-- **A positive diagonal matrix rescales the imaginary axis**: for `d = diag(a, b) ∈ GL(2, ℚ)`
with `ab > 0`, the weight-`2` slash by `d` restricts to the axis as `(F ∣[2] d) (i t) = r F (i r t)`
with `r = a / b > 0`, the rescaling `t ↦ r t` of the axis together with its Jacobian. -/
theorem resToImagAxis_slash_two_of_diagonal (F : ℍ → ℂ) {d : GL (Fin 2) ℚ} (h₁₀ : d 1 0 = 0)
    (h₀₁ : d 0 1 = 0) (hd : 0 < (d : Matrix (Fin 2) (Fin 2) ℚ).det) (t : ℝ) :
    resToImagAxis (F ∣[(2 : ℤ)] d) t =
      (((d 0 0 : ℝ) / d 1 1 : ℝ) : ℂ) * resToImagAxis F ((d 0 0 : ℝ) / d 1 1 * t) := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) ℚ).det = d 0 0 * d 1 1 := by
    rw [Matrix.det_fin_two, h₁₀, h₀₁]
    ring
  have hd' : 0 < d 0 0 * d 1 1 := hdet ▸ hd
  have h₁₁ : (d 1 1 : ℝ) ≠ 0 := by
    have : d 1 1 ≠ 0 := fun h ↦ by simp [h] at hd'
    exact_mod_cast this
  -- the axis is rescaled by the positive ratio `r = d₀₀ / d₁₁`
  set r : ℝ := (d 0 0 : ℝ) / d 1 1 with hr
  have hr0 : 0 < r := by
    have : (0 : ℚ) < d 0 0 / d 1 1 := div_pos_iff.mpr (mul_pos_iff.mp hd')
    rw [hr]
    exact_mod_cast this
  rcases le_or_gt t 0 with ht | ht
  · rw [resToImagAxis_of_nonpos _ ht, resToImagAxis_of_nonpos _ (by nlinarith), mul_zero]
  have hrt : 0 < r * t := mul_pos hr0 ht
  have hdet_pos : 0 < ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d).det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact ModularForm.det_map_ratCast_pos hd
  have hdetd : ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d).det : ℝ) =
      (d 0 0 : ℝ) * d 1 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_map_apply,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, eq_ratCast, Rat.cast_mul]
  rw [resToImagAxis_of_pos _ ht, resToImagAxis_of_pos _ hrt,
    ModularForm.rat_slash_apply_of_det_pos _ hd]
  -- `d` fixes `∞`, so its denominator is the constant `d₁₁`
  have hden : denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d)
      (⟨Complex.I * t, by simpa using ht⟩ : ℍ) = ((d 1 1 : ℝ) : ℂ) := by
    simp [denom, Matrix.GeneralLinearGroup.map_apply, h₁₀]
  -- `d` acts on the axis as the rescaling `i t ↦ i (r t)`
  have hsmul : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d •
      (⟨Complex.I * t, by simpa using ht⟩ : ℍ) =
        ⟨Complex.I * ((r * t : ℝ) : ℂ), by simpa using hrt⟩ := by
    ext1
    rw [coe_smul_of_det_pos hdet_pos, hden]
    simp only [num, Matrix.GeneralLinearGroup.map_apply, eq_ratCast, h₀₁, Rat.cast_zero, hr]
    push_cast
    ring
  -- the automorphy factor `det d ^ (2 - 1) · d₁₁ ^ (-2)` of `d` in weight `2` is the constant `r`
  have h21 : (2 : ℤ) - 1 = 1 := by norm_num
  have hc : ((((d 0 0 : ℝ) * (d 1 1 : ℝ) : ℝ)) : ℂ) ^ ((2 : ℤ) - 1) *
      ((d 1 1 : ℝ) : ℂ) ^ (-(2 : ℤ)) = (r : ℂ) := by
    rw [hr, h21, zpow_one, zpow_neg, zpow_two]
    push_cast
    field_simp
  rw [hsmul, hden, hdetd, abs_of_pos (by exact_mod_cast hd'), mul_assoc, hc, mul_comm]

open Asymptotics Filter in
/-- **A cusp form slashed by a rational matrix decays exponentially along the imaginary axis**:
`f ∣[k] g` is a cusp form on the conjugate level `g⁻¹ Γ g`, which is again arithmetic, so it has
the exponential decay of a cusp form at `i∞`. -/
theorem exists_isBigO_resToImagAxis_rat_slash_exp {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) :
    ∃ c > 0, resToImagAxis (f ∣[k] g) =O[atTop] fun t ↦ Real.exp (-c * t) := by
  set g' : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g with hg'
  -- the conjugate level is arithmetic; `Rat.castHom ℝ` and `algebraMap ℚ ℝ` are the same map
  have : (ConjAct.toConjAct g'⁻¹ • Γ).IsArithmetic := by
    simpa [hg', show Rat.castHom ℝ = algebraMap ℚ ℝ from rfl, map_inv]
      using Subgroup.IsArithmetic.conj Γ g⁻¹
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' (CuspForm.translate f g')
  refine ⟨c, hc, ?_⟩
  rw [CuspForm.coe_translate_gl] at hO
  rw [ModularForm.rat_slash]
  refine hO.resToImagAxis.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht]

end UpperHalfPlane
