/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.W1p.Truncation

/-!
# Weak maximum and comparison principles

For a coercive divergence-form energy form, a weak subsolution with nonpositive boundary data
is nonpositive almost everywhere. The boundary condition is expressed by membership of the
positive part in `W^{1,2}_0(Ω)`. It is meaningful on arbitrary open domains and requires no trace
operator or regularity of the boundary. The corresponding condition on `(u - v)⁺` gives the
weak comparison principle.

For `-div(a ∇u) + c u` on a domain contained in a ball, uniform ellipticity, bounded measurable
coefficients, and `c ≥ 0` suffice. The ball may have any centre; its radius does not impose a
smallness condition. The weak Dirichlet-solution corollary says that nonpositive forcing gives
a nonpositive solution whenever the energy form has a positive quadratic lower bound.

These are weak Sobolev maximum and comparison principles for Lane C, target 13 of
`TauCetiRoadmap/PDE/README.md`.

## Main declarations

* `TauCeti.PDE.value_nonpos_of_energyFormH1_nonpos`: the coercive weak maximum principle.
* `TauCeti.PDE.value_le_of_energyFormH1_le`: the coercive weak comparison principle.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_nonpos_of_energy_bound`: the sign of a weak solution.
* `TauCeti.PDE.UniformlyEllipticOn.value_nonpos_of_zero_drift_of_subset_ball`: the bounded-domain
  maximum principle without drift.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_of_zero_drift_of_subset_ball`: its comparison theorem.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-- Testing the energy form against the positive part of `u` gives the energy of that positive
part. This identity holds for all coefficients, without integrability assumptions. -/
theorem energyFormH1_posPart_right (u : W1p mu Omega 2) :
    energyFormH1 a b c u (W1p.posPart (by norm_num) u) =
      energyFormH1 a b c (W1p.posPart (by norm_num) u) (W1p.posPart (by norm_num) u) := by
  classical
  simp only [energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart (W1p.value u),
    W1p.gradient_posPart_ae (by norm_num) u] with x hv hg
  have hvalue : W1p.value (W1p.posPart (by norm_num) u) x = max (W1p.value u x) 0 := by
    rw [W1p.value_posPart]
    exact hv
  -- Membership in each indicator set below is exactly the positivity test on the value.
  by_cases hx : 0 < W1p.value u x
  · have hjet : jetField (W1p.posPart (by norm_num) u) x = jetField u x := by
      rw [jetField_apply, hvalue, hg, max_eq_left hx.le,
        indicator_of_mem (show x ∈ {y | 0 < W1p.value u y} from hx), jetField_apply]
    rw [hjet]
  · have hjet : jetField (W1p.posPart (by norm_num) u) x = 0 := by
      rw [jetField_apply, hvalue, hg, max_eq_right (le_of_not_gt hx),
        indicator_of_notMem (show x ∉ {y | 0 < W1p.value u y} from hx)]
      rfl
    rw [hjet]
    simp only [map_zero]

/-- A weak subsolution of a coercive divergence-form operator is nonpositive almost everywhere
if its positive part belongs to `W^{1,2}_0(Ω)`. The quadratic lower bound is required only on
the zero-boundary Sobolev space. -/
theorem value_nonpos_of_energyFormH1_nonpos {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ 0 := by
  let w : W1p0 mu Omega 2 := ⟨W1p.posPart (by norm_num) u, hboundary⟩
  have hvalue : ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (w : W1p mu Omega 2) x = max (W1p.value u x) 0 := by
    dsimp only [w]
    rw [W1p.value_posPart]
    exact Lp.coeFn_posPart (W1p.value u)
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x :=
    hvalue.mono fun x hx ↦ hx.symm ▸ le_max_right _ _
  have henergy := hu w hnonneg
  dsimp only [w] at henergy
  rw [energyFormH1_posPart_right] at henergy
  have hnorm : ‖w‖ = 0 := by
    have hbound := (hlower w).trans henergy
    apply le_antisymm ?_ (norm_nonneg w)
    exact le_of_not_gt fun hpos ↦ (not_lt_of_ge hbound) (mul_pos hC (pow_pos hpos 2))
  have hw : (w : W1p mu Omega 2) = 0 :=
    congrArg (fun v : W1p0 mu Omega 2 ↦ (v : W1p mu Omega 2)) (norm_eq_zero.mp hnorm)
  have hzero : W1p.value (w : W1p mu Omega 2) = 0 := by
    rw [hw, ← W1p.valueL_apply, map_zero]
  filter_upwards [hvalue, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := mu.restrict Omega)]
    with x hx hz
  rw [hzero, hz] at hx
  exact (le_max_left _ _).trans hx.symm.le

/-- Weak comparison for a coercive energy form: ordered weak operator values and
`(u - v)⁺ ∈ W^{1,2}_0(Ω)` imply `u ≤ v` almost everywhere. -/
theorem value_le_of_energyFormH1_le {u v : W1p mu Omega 2}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) ≤
          energyFormH1 a b c v (w : W1p mu Omega 2)) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  classical
  have hsub := value_nonpos_of_energyFormH1_nonpos hboundary hC hlower (by
    intro w hw
    rw [← energyFormH1L_apply hcoeff]
    simpa only [map_sub, sub_apply, energyFormH1L_apply] using
      sub_nonpos.mpr (huv w hw))
  have hvalue : W1p.value (u - v) = W1p.value u - W1p.value v := by
    simp only [← W1p.valueL_apply, map_sub]
  filter_upwards [hsub, Lp.coeFn_sub (W1p.value u) (W1p.value v)] with x hx hval
  rw [hvalue, hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

/-- A homogeneous weak Dirichlet solution with nonpositive forcing is nonpositive almost
everywhere when the energy form has a positive quadratic lower bound on `W^{1,2}_0(Ω)`. -/
theorem IsWeakSolutionDirichlet.value_nonpos_of_energy_bound
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hf : ∀ᵐ x ∂mu.restrict Omega, f x ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value (u : W1p mu Omega 2) x ≤ 0 := by
  refine TauCeti.PDE.value_nonpos_of_energyFormH1_nonpos
    (W1p.posPart_mem_w1p0Submodule (by norm_num) u.property) hC hlower ?_
  intro v hv
  rw [(isWeakSolutionDirichlet_iff f u).mp hu v]
  exact integral_nonpos_of_ae (hf.and hv |>.mono fun x hx ↦
    mul_nonpos_of_nonpos_of_nonneg hx.1 hx.2)

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam gamma : ℝ}

/-- The weak maximum principle for `-div(a ∇u) + c u` on a ball-contained domain, with
uniformly elliptic `a`, bounded measurable coefficients, and `c ≥ 0`. Nonpositive boundary
data means that `u⁺` belongs to `W^{1,2}_0(Ω)`; no boundary regularity is assumed. -/
theorem UniformlyEllipticOn.value_nonpos_of_zero_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    {u : W1p volume Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ v : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (v : W1p volume Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p volume Omega 2) ≤ 0) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ 0 := by
  refine value_nonpos_of_energyFormH1_nonpos hboundary
    (div_pos h.pos (by positivity : 0 < (2 * R) ^ 2 + 1)) ?_ hu
  intro w
  exact h.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift ha hc (by simp) hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball (by norm_num) hOmega w.property)

/-- Weak comparison for `-div(a ∇u) + c u` on a ball-contained domain. Ordered weak operator
values and `(u - v)⁺ ∈ W^{1,2}_0(Ω)` imply `u ≤ v` almost everywhere. The potential is bounded
and nonnegative, and the leading coefficients are bounded, measurable, and uniformly elliptic. -/
theorem UniformlyEllipticOn.value_le_of_zero_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    {u v : W1p volume Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule volume Omega 2)
    (huv : ∀ w : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (w : W1p volume Omega 2) x) →
        energyFormH1 a 0 c u (w : W1p volume Omega 2) ≤
          energyFormH1 a 0 c v (w : W1p volume Omega 2)) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (beta := 0) h.upper_nonneg ha
    aestronglyMeasurable_const hc (fun x hx eta xi ↦ h.upper_bound hx eta xi)
    (by simp) hc_bound
  refine value_le_of_energyFormH1_le hcoeff hboundary
    (div_pos h.pos (by positivity : 0 < (2 * R) ^ 2 + 1)) ?_ huv
  intro w
  exact h.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift ha hc (by simp) hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball (by norm_num) hOmega w.property)

end Euclidean

end TauCeti.PDE
