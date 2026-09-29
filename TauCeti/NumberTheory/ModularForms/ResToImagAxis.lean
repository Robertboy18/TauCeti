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
