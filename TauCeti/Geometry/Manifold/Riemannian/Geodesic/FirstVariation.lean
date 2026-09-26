/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricIntegral
public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# The energy of a curve and its first variation

The *energy* of a curve `γ` in a Riemannian manifold between the parameters `a` and `b` is
`E(γ) = ½ ∫_a^b ‖γ'(t)‖² dt`.  A *variation* of `γ` is a two-parameter family `F` with `F 0 = γ`;
its *variation field* is the transverse velocity `V(t) = ∂F/∂s (0, t)`, a tangent vector at
`γ t`.  This file computes the derivative at `s = 0` of the energy of the curves `F s`:

`d/ds E(F s) |₀ = ⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`,

where `D_t γ'` is the covariant acceleration of `γ` for the Levi-Civita connection.  When the
variation fixes the endpoints the boundary terms vanish, and along a geodesic the integral
vanishes too: geodesics are critical points of the energy among fixed-endpoint variations.

The formula only asks the family to be `C²` at the points of `{0} × [a, b]`.  The proof
differentiates under the integral sign, which is legitimate because the squared speed of `F s`
is jointly `C¹` in `(s, t)` near the compact segment, then uses metric compatibility along the
transverse curves to bring the `s`-derivative onto the velocity field, the symmetry lemma for the
mixed covariant derivatives of a parametrized surface to exchange the two derivatives, and metric
compatibility along `γ` to integrate by parts.

## Main definitions and results

* `TauCeti.Manifold.energy`: the energy of a curve between two parameters.
* `TauCeti.Manifold.IsGeodesicCurveOn.energy_eq`: the energy of a geodesic segment is
  `(b - a) ‖γ'(a)‖² / 2`.
* `TauCeti.Manifold.variationField`: the variation field of a two-parameter family.
* `TauCeti.Manifold.hasDerivAt_energy`: **the first variation formula** for the energy, with
  boundary terms.
* `TauCeti.Manifold.hasDerivAt_energy_of_fixed_endpoints`: the first variation formula for a
  variation fixing the endpoints.
* `TauCeti.Manifold.IsGeodesicCurveOn.hasDerivAt_energy_zero`: **geodesics are critical
  points of the energy** among variations with fixed endpoints.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, Proposition 2.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12, the energy
  of a path and its first variation.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6, the first
  variation formula for length, whose proof follows the same scheme.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Variations and their variation fields

A variation is a two-parameter family `F : ℝ → ℝ → M`, whose first argument is the variation
parameter `s` and whose second argument is the curve parameter `t`; the varied curve is `F 0`.
Hypotheses on a variation are stated on the uncurried map `fun z : ℝ × ℝ ↦ F z.1 z.2`. -/

variable (I) in
/-- The **variation field** of a two-parameter family `F`: the velocity at `s = 0` of the
transverse curve `s ↦ F s t`, a tangent vector at `F 0 t`.  In the classical notation it is
`V(t) = ∂F/∂s (0, t)`. -/
def variationField (F : ℝ → ℝ → M) (t : ℝ) : TangentSpace I (F 0 t) :=
  curveVelocity I (fun s ↦ F s t) 0

/-- The defining formula for the variation field. -/
theorem variationField_apply (F : ℝ → ℝ → M) (t : ℝ) :
    variationField I F t = curveVelocity I (fun s ↦ F s t) 0 :=
  (rfl)

/-- At a parameter where every curve of the family passes through the same point, the variation
field vanishes. -/
theorem variationField_eq_zero {F : ℝ → ℝ → M} {t : ℝ} (h : ∀ s, F s t = F 0 t) :
    variationField I F t = 0 := by
  have hfun : (fun s ↦ F s t) = fun _ ↦ F 0 t := funext h
  rw [variationField_apply, hfun, curveVelocity_const]

section Partial

variable {F : ℝ → ℝ → M}

/-- The velocity of a curve of the family is the differential of the uncurried family in the
direction of the curve parameter. -/
private theorem curveVelocity_eq_mfderiv_snd {s t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t)) :
    curveVelocity I (F s) t =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) ((0 : ℝ), (1 : ℝ)) :=
  hf.curveVelocity_comp_mfderiv (g := fun r : ℝ ↦ (s, r))
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

/-- The transverse velocity of the family is the differential of the uncurried family in the
direction of the variation parameter. -/
private theorem curveVelocity_eq_mfderiv_fst {s t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t)) :
    curveVelocity I (fun q ↦ F q t) s =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) ((1 : ℝ), (0 : ℝ)) :=
  hf.curveVelocity_comp_mfderiv (g := fun q : ℝ ↦ (q, t))
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))

variable [IsManifold I 2 M]

/-- A family which is `C²` at every point of the segment `{0} × [a, b]` is `C²` on a product of
open neighbourhoods of `0` and of `[a, b]`. -/
private theorem exists_isOpen_prod_contMDiffOn {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ∃ U V : Set ℝ, IsOpen U ∧ IsOpen V ∧ (0 : ℝ) ∈ U ∧ uIcc a b ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) := by
  -- the set where the family is `C²` is open, since `C²` at a point means `C²` near it
  have hWo : IsOpen {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨u, hu, hfu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hz
    filter_upwards [interior_mem_nhds.mpr hu] with y hy
    exact hfu.contMDiffAt (mem_interior_iff_mem_nhds.mp hy)
  have hW : {(0 : ℝ)} ×ˢ uIcc a b ⊆
      {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    rw [mem_singleton_iff] at hs
    subst hs
    exact hF t ht
  obtain ⟨U, V, hUo, hVo, hU0, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hWo hW
  exact ⟨U, V, hUo, hVo, hU0 (mem_singleton 0), hV, fun z hz ↦ (hUV hz).contMDiffWithinAt⟩

end Partial

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-! ### The energy functional -/

variable (I) in
/-- The **energy** of a curve `γ` between the parameters `a` and `b`: half the integral of its
squared Riemannian speed, `E(γ) = ½ ∫_a^b ‖γ'(t)‖² dt`.  It is meant for curves which are `C¹`
near `[a, b]`; for other curves the integrand may take junk values. -/
def energy (γ : ℝ → M) (a b : ℝ) : ℝ :=
  (∫ t in a..b, ‖curveVelocity I γ t‖ ^ 2) / 2

/-- The defining formula for the energy. -/
theorem energy_def (γ : ℝ → M) (a b : ℝ) :
    energy I γ a b = (∫ t in a..b, ‖curveVelocity I γ t‖ ^ 2) / 2 :=
  (rfl)

/-- A constant curve has zero energy. -/
@[simp]
theorem energy_const (x : M) (a b : ℝ) : energy I (fun _ : ℝ ↦ x) a b = 0 := by
  simp [energy_def, curveVelocity_const]

/-- The energy over a degenerate parameter interval vanishes. -/
@[simp]
theorem energy_self (γ : ℝ → M) (a : ℝ) : energy I γ a a = 0 := by
  simp [energy_def]

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The energy of a geodesic segment.** A geodesic has constant speed, so its energy between
`a` and `b` is `(b - a) ‖γ'(a)‖² / 2`. -/
theorem IsGeodesicCurveOn.energy_eq {γ : ℝ → M} {s : Set ℝ} (h : IsGeodesicCurveOn I γ s)
    (hs : IsOpen s) (hconn : IsPreconnected s) {a b : ℝ} (hsub : uIcc a b ⊆ s) :
    energy I γ a b = (b - a) * ‖curveVelocity I γ a‖ ^ 2 / 2 := by
  have ha : a ∈ s := hsub left_mem_uIcc
  have key : EqOn (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) (fun _ ↦ ‖curveVelocity I γ a‖ ^ 2)
      (uIcc a b) := by
    intro t ht
    have ht' : t ∈ s := hsub ht
    simp only
    rw [← curveVelocityWithin_of_mem_nhds (hs.mem_nhds ht'),
      ← curveVelocityWithin_of_mem_nhds (hs.mem_nhds ha),
      h.norm_curveVelocityWithin_eq hconn ht' ha]
  rw [energy_def, intervalIntegral.integral_congr key, intervalIntegral.integral_const,
    smul_eq_mul]

/-! ### The first variation of energy -/

section FirstVariation

variable {F : ℝ → ℝ → M}

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- On an open set where the family is `C²`, the Riemannian inner product of two of its lifted
directional derivatives is jointly `C¹`. -/
private theorem contDiffOn_inner_mfderiv {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) W) (ξ η : ℝ × ℝ) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ ↦
      inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ξ)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z η)) W := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact ContMDiffOn.inner_bundle (hf.contMDiffOn_mk_mfderiv_apply (by norm_num) hW ξ)
    (hf.contMDiffOn_mk_mfderiv_apply (by norm_num) hW η)

/-- **The transverse derivative of the squared speed.** At a parameter where the family is `C²`,
the derivative at `s = 0` of the squared speed of `F s` at `t` is `2 ⟪D_t V, γ'⟫`, where `V` is
the variation field and `γ = F 0`: metric compatibility along the transverse curve gives
`2 ⟪D_s ∂_t F, ∂_t F⟫`, and the symmetry lemma exchanges the two covariant derivatives. -/
private theorem hasDerivAt_norm_sq_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2)
      (2 * inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
        (fun r ↦ curveVelocity I (fun q ↦ F q r) 0) t) (curveVelocity I (F 0) t)) 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
  have hPcoord := hf.differentiableAt_sectionCoord_curveVelocity_snd (f := F) hbase
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) 0 :=
    (hf.comp 0 (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 2) t)).contMDiffAt)
      |>.mdifferentiableAt two_ne_zero
  have hprod := (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve hcurve hPcoord hPcoord
  have hswap := alongCurve_curveVelocity_comm (leviCivitaConnection I M)
    ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I))
    (f := F) (u := 0) (v := t) (hf.of_le (by simp))
  rw [← hswap, real_inner_comm (curveVelocity I (F 0) t), ← two_mul, real_inner_comm] at hprod
  exact hprod.congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ (real_inner_self_eq_norm_sq _).symm)

/-- **The product rule for the variation field against the velocity.** At a parameter where the
family is `C²`, the function `t ↦ ⟪V(t), γ'(t)⟫` has derivative `⟪D_t V, γ'⟫ + ⟪V, D_t γ'⟫`. -/
private theorem hasDerivAt_inner_variationField_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun r ↦ inner ℝ (curveVelocity I (fun q ↦ F q r) 0) (curveVelocity I (F 0) r))
      (inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ curveVelocity I (fun q ↦ F q r) 0) t) (curveVelocity I (F 0) t) +
        inner ℝ (curveVelocity I (fun q ↦ F q t) 0)
          (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) t := by
  have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
  have hVcoord := hf.differentiableAt_sectionCoord_curveVelocity_fst (f := F) hbase
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (F 0) t :=
    hf.comp t (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) (0 : ℝ))).contMDiffAt
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγt
  have hγcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := F 0)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  exact (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve (hγt.mdifferentiableAt two_ne_zero) hVcoord hγcoord

/-- **The first variation of energy.** Let `F` be a two-parameter family which is `C²` at every
point of `{0} × [a, b]`, with central curve `γ = F 0` and variation field `V`.  Then the energy
of `F s` between `a` and `b` is differentiable at `s = 0`, with derivative

`⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`,

where `D_t γ'` is the covariant acceleration of `γ` for the Levi-Civita connection. -/
theorem hasDerivAt_energy {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun s ↦ energy I (F s) a b)
      (inner ℝ (variationField I F b) (curveVelocity I (F 0) b) -
        inner ℝ (variationField I F a) (curveVelocity I (F 0) a) -
        ∫ t in a..b, inner ℝ (variationField I F t)
          (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) 0 := by
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ := exists_isOpen_prod_contMDiffOn hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  have hsurf : ∀ {s t : ℝ}, s ∈ U → t ∈ V →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) :=
    fun hs ht ↦ hfUV.contMDiffAt (hUVo.mem_nhds ⟨hs, ht⟩)
  -- The squared speed `G` and the mixed inner product `K` of the partial velocities, as jointly
  -- `C¹` functions of `(s, t)` on `U ×ˢ V`.
  set G : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ))) with hG_def
  set K : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((1 : ℝ), (0 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ))) with hK_def
  have hG : ContDiffOn ℝ 1 G (U ×ˢ V) := contDiffOn_inner_mfderiv hUVo hfUV _ _
  have hK : ContDiffOn ℝ 1 K (U ×ˢ V) := contDiffOn_inner_mfderiv hUVo hfUV _ _
  have hGeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 := by
    intro s t hs ht
    rw [← real_inner_self_eq_norm_sq,
      curveVelocity_eq_mfderiv_snd ((hsurf hs ht).mdifferentiableAt two_ne_zero)]
  have hKeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V →
      K (s, t) = inner ℝ (curveVelocity I (fun q ↦ F q t) s) (curveVelocity I (F s) t) := by
    intro s t hs ht
    rw [curveVelocity_eq_mfderiv_snd ((hsurf hs ht).mdifferentiableAt two_ne_zero),
      curveVelocity_eq_mfderiv_fst ((hsurf hs ht).mdifferentiableAt two_ne_zero)]
  -- Differentiation under the integral sign: near `s = 0` the energy is `½ ∫ G (s, t) dt`.
  have henergy : (fun s ↦ energy I (F s) a b) =ᶠ[𝓝 0] fun s ↦ (∫ t in a..b, G (s, t)) / 2 := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    rw [energy_def]
    congr 1
    exact intervalIntegral.integral_congr fun t ht ↦ (hGeq hs (hV ht)).symm
  have hmain : HasDerivAt (fun s ↦ energy I (F s) a b)
      ((∫ t in a..b, fderiv ℝ G (0, t) (1, 0)) / 2) 0 :=
    ((TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo hG (prod_mono
      (singleton_subset_iff.mpr h0U) hV)).div_const 2).congr_of_eventuallyEq henergy
  -- The `t`-derivative of `t ↦ K (0, t) = ⟪V(t), γ'(t)⟫` is continuous on `V`.
  have hK0 : ContDiffOn ℝ 1 (fun r ↦ K (0, r)) V :=
    hK.comp (contDiff_prodMk_right (0 : ℝ)).contDiffOn fun r hr ↦ ⟨h0U, hr⟩
  have hK0deriv : ∀ r ∈ V, HasDerivAt (fun r ↦ K (0, r)) (deriv (fun r ↦ K (0, r)) r) r :=
    fun r hr ↦ ((hK0.differentiableOn one_ne_zero r hr).differentiableAt
      (hVo.mem_nhds hr)).hasDerivAt
  have hK0cont : ContinuousOn (deriv fun r ↦ K (0, r)) V :=
    hK0.continuousOn_deriv_of_isOpen hVo le_rfl
  have hG'cont : ContinuousOn (fun t ↦ fderiv ℝ G (0, t) (1, 0)) V :=
    ((hG.continuousOn_fderiv_of_isOpen hUVo le_rfl).clm_apply continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn fun r hr ↦ ⟨h0U, hr⟩
  -- Pointwise on `V`: `½ ∂ₛ G (0, t) = d/dt K (0, t) - ⟪V(t), D_t γ'(t)⟫`.
  have hpt : ∀ t ∈ V, fderiv ℝ G (0, t) (1, 0) / 2 =
      deriv (fun r ↦ K (0, r)) t - inner ℝ (curveVelocity I (fun q ↦ F q t) 0)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t) := by
    intro t ht
    have hz : ((0 : ℝ), t) ∈ U ×ˢ V := ⟨h0U, ht⟩
    have hGz : HasFDerivAt G (fderiv ℝ G (0, t)) (0, t) :=
      ((hG.differentiableOn one_ne_zero _ hz).differentiableAt (hUVo.mem_nhds hz)).hasFDerivAt
    have hpath : HasDerivAt (fun s : ℝ ↦ (s, t)) ((1 : ℝ), (0 : ℝ)) 0 :=
      (hasDerivAt_id' (x := (0 : ℝ))).prodMk (hasDerivAt_const (0 : ℝ) t)
    have hGs : HasDerivAt (fun s ↦ G (s, t)) (fderiv ℝ G (0, t) (1, 0)) 0 := by
      exact hGz.comp_hasDerivAt (0 : ℝ) hpath
    have hGeq' : (fun s ↦ G (s, t)) =ᶠ[𝓝 0] fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2 := by
      filter_upwards [hUo.mem_nhds h0U] with s hs
      exact hGeq hs ht
    have hKeq' : (fun r ↦ K (0, r)) =ᶠ[𝓝 t]
        fun r ↦ inner ℝ (curveVelocity I (fun q ↦ F q r) 0) (curveVelocity I (F 0) r) := by
      filter_upwards [hVo.mem_nhds ht] with r hr
      exact hKeq h0U hr
    have h1 := hGs.unique
      ((hasDerivAt_norm_sq_curveVelocity (hsurf h0U ht)).congr_of_eventuallyEq hGeq')
    have h2 := (hK0deriv t ht).unique
      ((hasDerivAt_inner_variationField_curveVelocity (hsurf h0U ht)).congr_of_eventuallyEq
        hKeq')
    rw [h1, h2]
    ring
  -- Integrate the pointwise identity; the fundamental theorem of calculus evaluates the
  -- derivative term at the endpoints.
  have hK'int : IntervalIntegrable (deriv fun r ↦ K (0, r)) volume a b :=
    (hK0cont.mono hV).intervalIntegrable
  have hVAint : IntervalIntegrable (fun t ↦ inner ℝ (curveVelocity I (fun q ↦ F q t) 0)
      (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) volume a b := by
    refine (((hK0cont.mono hV).sub ((hG'cont.mono hV).div_const 2)).congr ?_).intervalIntegrable
    intro t ht
    simp only [Pi.sub_apply]
    rw [hpt t (hV ht)]
    ring
  have hFTC : ∫ t in a..b, deriv (fun r ↦ K (0, r)) t = K (0, b) - K (0, a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hK0deriv t (hV ht)) hK'int
  refine hmain.congr_deriv ?_
  calc (∫ t in a..b, fderiv ℝ G (0, t) (1, 0)) / 2
      = ∫ t in a..b, fderiv ℝ G (0, t) (1, 0) / 2 := (intervalIntegral.integral_div 2 _).symm
    _ = ∫ t in a..b, (deriv (fun r ↦ K (0, r)) t - inner ℝ (curveVelocity I (fun q ↦ F q t) 0)
          (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) :=
        intervalIntegral.integral_congr fun t ht ↦ hpt t (hV ht)
    _ = (∫ t in a..b, deriv (fun r ↦ K (0, r)) t) -
          ∫ t in a..b, inner ℝ (curveVelocity I (fun q ↦ F q t) 0)
            (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t) :=
        intervalIntegral.integral_sub hK'int hVAint
    _ = _ := by
        rw [hFTC, hKeq h0U (hV right_mem_uIcc), hKeq h0U (hV left_mem_uIcc)]
        simp only [variationField_apply]

/-- **The first variation of energy for a variation with fixed endpoints.** If moreover every
curve of the family has the same endpoints as `γ = F 0`, the derivative at `s = 0` of the energy
is `-∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`. -/
theorem hasDerivAt_energy_of_fixed_endpoints {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (ha : ∀ s, F s a = F 0 a) (hb : ∀ s, F s b = F 0 b) :
    HasDerivAt (fun s ↦ energy I (F s) a b)
      (-∫ t in a..b, inner ℝ (variationField I F t)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) 0 := by
  refine (hasDerivAt_energy hF).congr_deriv ?_
  rw [variationField_eq_zero ha, variationField_eq_zero hb, inner_zero_left, inner_zero_left]
  ring

/-- **Geodesics are critical points of the energy.** If the central curve `γ = F 0` of a
variation with fixed endpoints is a geodesic on an open set containing `[a, b]`, the derivative
at `s = 0` of the energy of `F s` vanishes. -/
theorem IsGeodesicCurveOn.hasDerivAt_energy_zero {a b : ℝ} {s : Set ℝ}
    (h : IsGeodesicCurveOn I (F 0) s) (hs : IsOpen s) (hsub : uIcc a b ⊆ s)
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (ha : ∀ s, F s a = F 0 a) (hb : ∀ s, F s b = F 0 b) :
    HasDerivAt (fun s ↦ energy I (F s) a b) 0 0 := by
  refine (hasDerivAt_energy_of_fixed_endpoints hF ha hb).congr_deriv ?_
  rw [neg_eq_zero]
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
    intervalIntegral.integral_zero
  simp only [((isGeodesicCurveOn_iff_of_isOpen hs).mp h).2 t (hsub ht), inner_zero_right]

end FirstVariation

end TauCeti.Manifold

end
