/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Vitali's convergence theorem for maps into a pseudometric space

Let `μ` be a finite measure on `X` and let `T n, T₀ : X → Y` be almost-everywhere measurable
maps into a second-countable pseudometric space. Mathlib's Vitali convergence theorem
`MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite` characterises `Lᵖ` convergence of
vector-valued functions as convergence in measure together with uniform integrability. This file
transports it to `Y`-valued maps through the real-valued distances: for `1 ≤ p < ∞` and maps with
finite `p`-th moment about a basepoint `y₀`, the distances `dist (T n x) (T₀ x)` converge to `0`
in `Lᵖ(μ)` exactly when `T n` converges to `T₀` in measure and the family `dist (T n ·) y₀` is
uniformly integrable in `Lᵖ(μ)`.

The uniform integrability of `dist (T n ·) y₀` does not depend on the basepoint `y₀`: by the
triangle inequality, changing the basepoint changes each distance by at most the constant
`dist y₀ y₁`, and constants are uniformly integrable over a finite measure. Uniform integrability is
Mathlib's `MeasureTheory.UnifIntegrable`, the predicate its Vitali theorem uses, or equivalently
`MeasureTheory.UniformIntegrable`, which adds a uniform `Lᵖ` bound; in the convergence theorem the
bound follows from the `Lᵖ` convergence, since a convergent sequence of finite norms is bounded.

## Main statements

* `TauCeti.memLp_dist_of_memLp_dist` — two maps with finite `p`-th moment about a basepoint have
  a distance with finite `p`-th moment;
* `TauCeti.unifIntegrable_dist_iff_dist` and `TauCeti.uniformIntegrable_dist_iff_dist` — uniform
  integrability of the distances to a basepoint does not depend on the basepoint;
* `TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable` — **Vitali's theorem
  for maps into a pseudometric space**: for `1 ≤ p < ∞`, `Lᵖ` convergence of `dist (T n ·) (T₀ ·)`
  to `0` is convergence in measure together with uniform integrability of `dist (T n ·) y₀`;
* `TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_uniformIntegrable` — the same with
  `MeasureTheory.UniformIntegrable`, which also records the uniform `Lᵖ` bound.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, second edition, Birkhäuser 2008, Lemma 5.4.1, whose `Lᵖ` refinement is
  the statement proved here.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [PseudoMetricSpace Y]

/-- The triangle inequality `dist a c ≤ dist a b + dist b c` between norms of real numbers, in
the form `MeasureTheory.eLpNorm_mono_ae` and `MeasureTheory.UnifIntegrable.ae_mono` consume. -/
private theorem norm_dist_le_norm_dist_add_dist (a b c : Y) :
    ‖dist a c‖ ≤ ‖dist a b + dist b c‖ := by
  rw [Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
  exact dist_triangle a b c

/-- The triangle inequality `dist a b ≤ dist a c + dist b c` between norms of real numbers, in
the form `MeasureTheory.MemLp.of_le` and `MeasureTheory.UnifIntegrable.ae_mono` consume. -/
private theorem norm_dist_le_norm_dist_add_dist_right (a b c : Y) :
    ‖dist a b‖ ≤ ‖dist a c + dist b c‖ := by
  rw [Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
  exact dist_triangle_right a b c

variable [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology Y] {μ : Measure X} {p : ℝ≥0∞}

section MemLp

variable {T T₀ : X → Y} {y₀ : Y}

/-- Two almost-everywhere measurable maps with finite `p`-th moment about a basepoint `y₀` have a
distance with finite `p`-th moment. -/
theorem memLp_dist_of_memLp_dist (hT : AEMeasurable T μ) (hT₀ : AEMeasurable T₀ μ)
    (hTp : MemLp (fun x ↦ dist (T x) y₀) p μ) (hT₀p : MemLp (fun x ↦ dist (T₀ x) y₀) p μ) :
    MemLp (fun x ↦ dist (T x) (T₀ x)) p μ :=
  (hTp.add hT₀p).of_le (hT.dist hT₀).aestronglyMeasurable <|
    ae_of_all _ fun x ↦ norm_dist_le_norm_dist_add_dist_right (T x) (T₀ x) y₀

end MemLp

section Basepoint

variable [IsFiniteMeasure μ] {ι : Type*} {T : ι → X → Y} {y₀ y₁ : Y}

/-- Uniform integrability in `Lᵖ(μ)` of the distances `dist (T i ·) y₀` does not depend on the
basepoint `y₀`, for `1 ≤ p < ∞` and a finite measure `μ`: changing the basepoint changes each
distance by at most the constant `dist y₀ y₁`. -/
theorem unifIntegrable_dist_iff_dist (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ i, AEMeasurable (T i) μ) :
    UnifIntegrable (fun i x ↦ dist (T i x) y₀) p μ ↔
      UnifIntegrable (fun i x ↦ dist (T i x) y₁) p μ := by
  suffices key : ∀ y₀ y₁ : Y, UnifIntegrable (fun i x ↦ dist (T i x) y₀) p μ →
      UnifIntegrable (fun i x ↦ dist (T i x) y₁) p μ from ⟨key y₀ y₁, key y₁ y₀⟩
  intro y₀ y₁ h
  exact (h.add (unifIntegrable_const hp hp' (memLp_const (dist y₀ y₁))) hp
    (fun i ↦ ((hT i).dist aemeasurable_const).aestronglyMeasurable)
    fun _ ↦ aestronglyMeasurable_const).ae_mono fun i ↦ ae_of_all _ fun x ↦
      enorm_le_iff_norm_le.2 (norm_dist_le_norm_dist_add_dist (T i x) y₀ y₁)

/-- Uniform integrability in `Lᵖ(μ)` with a uniform `Lᵖ` bound of the distances `dist (T i ·) y₀`
does not depend on the basepoint `y₀`, for `1 ≤ p < ∞` and a finite measure `μ`. -/
theorem uniformIntegrable_dist_iff_dist (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ i, AEMeasurable (T i) μ) :
    UniformIntegrable (fun i x ↦ dist (T i x) y₀) p μ ↔
      UniformIntegrable (fun i x ↦ dist (T i x) y₁) p μ := by
  suffices key : ∀ y₀ y₁ : Y, UniformIntegrable (fun i x ↦ dist (T i x) y₀) p μ →
      UniformIntegrable (fun i x ↦ dist (T i x) y₁) p μ from ⟨key y₀ y₁, key y₁ y₀⟩
  rintro y₀ y₁ ⟨-, hui, C, hC⟩
  refine ⟨fun i ↦ ((hT i).dist aemeasurable_const).aestronglyMeasurable,
    (unifIntegrable_dist_iff_dist hp hp' hT).1 hui,
    C + (eLpNorm (fun _ : X ↦ dist y₀ y₁) p μ).toNNReal, fun i ↦ ?_⟩
  calc eLpNorm (fun x ↦ dist (T i x) y₁) p μ
      ≤ eLpNorm ((fun x ↦ dist (T i x) y₀) + fun _ ↦ dist y₀ y₁) p μ :=
        eLpNorm_mono_ae <| ae_of_all _ fun x ↦ norm_dist_le_norm_dist_add_dist (T i x) y₀ y₁
    _ ≤ eLpNorm (fun x ↦ dist (T i x) y₀) p μ + eLpNorm (fun _ : X ↦ dist y₀ y₁) p μ :=
        eLpNorm_add_le ((hT i).dist aemeasurable_const).aestronglyMeasurable
          aestronglyMeasurable_const hp
    _ ≤ C + (eLpNorm (fun _ : X ↦ dist y₀ y₁) p μ).toNNReal := by
        rw [ENNReal.coe_toNNReal (memLp_const _).eLpNorm_ne_top]
        exact add_le_add_left (hC i) _

end Basepoint

section Vitali

variable [IsFiniteMeasure μ] {T : ℕ → X → Y} {T₀ : X → Y} {y₀ : Y}

/-- **Vitali's convergence theorem for maps into a pseudometric space.** Let `1 ≤ p < ∞`, let
`μ` be a finite measure, and let the almost-everywhere measurable maps `T n, T₀ : X → Y` have
finite `p`-th moment about a point `y₀`. Then `dist (T n x) (T₀ x)` tends to `0` in `Lᵖ(μ)` if
and only if `T n` converges to `T₀` in `μ`-measure and the family `dist (T n ·) y₀` is uniformly
integrable in `Lᵖ(μ)`. -/
theorem tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ n, AEMeasurable (T n) μ) (hT₀ : AEMeasurable T₀ μ)
    (hTp : ∀ n, MemLp (fun x ↦ dist (T n x) y₀) p μ) (hT₀p : MemLp (fun x ↦ dist (T₀ x) y₀) p μ) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ) atTop (𝓝 0) ↔
      TendstoInMeasure μ T atTop T₀ ∧ UnifIntegrable (fun n x ↦ dist (T n x) y₀) p μ := by
  -- convergence in measure of the maps is convergence in measure of their distances to `0`
  have key : TendstoInMeasure μ T atTop T₀ ↔
      TendstoInMeasure μ (fun n x ↦ dist (T n x) (T₀ x)) atTop 0 := by
    simp only [tendstoInMeasure_iff_dist, Pi.zero_apply, Real.dist_0_eq_abs, abs_dist]
  have hdp : ∀ n, MemLp (fun x ↦ dist (T n x) (T₀ x)) p μ := fun n ↦
    memLp_dist_of_memLp_dist (hT n) hT₀ (hTp n) hT₀p
  have hd₀ : UnifIntegrable (fun _ : ℕ ↦ fun x ↦ dist (T₀ x) y₀) p μ :=
    unifIntegrable_const hp hp' hT₀p
  -- Vitali's theorem for the distances, then transport of uniform integrability along the two
  -- triangle inequalities
  have hV := tendstoInMeasure_iff_tendsto_Lp_finite hp hp' hdp (MemLp.zero (p := p) (μ := μ))
  simp only [sub_zero] at hV
  rw [← hV, key]
  refine and_congr_right fun _ ↦ ⟨fun hui ↦ ?_, fun hui ↦ ?_⟩
  · exact (hui.add hd₀ hp (fun n ↦ (hdp n).aestronglyMeasurable)
      fun _ ↦ hT₀p.aestronglyMeasurable).ae_mono fun n ↦ ae_of_all _ fun x ↦
        enorm_le_iff_norm_le.2 (norm_dist_le_norm_dist_add_dist (T n x) (T₀ x) y₀)
  · exact (hui.add hd₀ hp (fun n ↦ (hTp n).aestronglyMeasurable)
      fun _ ↦ hT₀p.aestronglyMeasurable).ae_mono fun n ↦ ae_of_all _ fun x ↦
        enorm_le_iff_norm_le.2 (norm_dist_le_norm_dist_add_dist_right (T n x) (T₀ x) y₀)

/-- **Vitali's convergence theorem for maps into a pseudometric space**, with
`MeasureTheory.UniformIntegrable`: under the hypotheses of
`TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable`, `dist (T n x) (T₀ x)`
tends to `0` in `Lᵖ(μ)` if and only if `T n` converges to `T₀` in `μ`-measure and the family
`dist (T n ·) y₀` is uniformly integrable in `Lᵖ(μ)` with a uniform `Lᵖ` bound. -/
theorem tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_uniformIntegrable (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hT : ∀ n, AEMeasurable (T n) μ) (hT₀ : AEMeasurable T₀ μ)
    (hTp : ∀ n, MemLp (fun x ↦ dist (T n x) y₀) p μ) (hT₀p : MemLp (fun x ↦ dist (T₀ x) y₀) p μ) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ) atTop (𝓝 0) ↔
      TendstoInMeasure μ T atTop T₀ ∧ UniformIntegrable (fun n x ↦ dist (T n x) y₀) p μ := by
  refine ⟨fun hL ↦ ?_, fun ⟨hTm, hui⟩ ↦
    (tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable hp hp' hT hT₀ hTp hT₀p).2
      ⟨hTm, hui.unifIntegrable⟩⟩
  obtain ⟨hTm, hui⟩ :=
    (tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable hp hp' hT hT₀ hTp hT₀p).1 hL
  refine ⟨hTm, fun n ↦ (hTp n).aestronglyMeasurable, hui, ?_⟩
  have hdp : ∀ n, MemLp (fun x ↦ dist (T n x) (T₀ x)) p μ := fun n ↦
    memLp_dist_of_memLp_dist (hT n) hT₀ (hTp n) hT₀p
  -- the convergent sequence of finite `Lᵖ` norms of the distances is bounded
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ n, eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ ≤ C := by
    have ht : Tendsto (fun n ↦ (eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ).toNNReal) atTop
        (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp hL
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    exact ⟨C, fun n ↦ by
      rw [← ENNReal.coe_toNNReal (hdp n).eLpNorm_ne_top]
      exact ENNReal.coe_le_coe.2 (hC ⟨n, rfl⟩)⟩
  refine ⟨C + (eLpNorm (fun x ↦ dist (T₀ x) y₀) p μ).toNNReal, fun n ↦ ?_⟩
  calc eLpNorm (fun x ↦ dist (T n x) y₀) p μ
      ≤ eLpNorm ((fun x ↦ dist (T n x) (T₀ x)) + fun x ↦ dist (T₀ x) y₀) p μ :=
        eLpNorm_mono_ae <| ae_of_all _ fun x ↦ norm_dist_le_norm_dist_add_dist (T n x) (T₀ x) y₀
    _ ≤ eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ + eLpNorm (fun x ↦ dist (T₀ x) y₀) p μ :=
        eLpNorm_add_le (hdp n).aestronglyMeasurable hT₀p.aestronglyMeasurable hp
    _ ≤ C + (eLpNorm (fun x ↦ dist (T₀ x) y₀) p μ).toNNReal := by
        rw [ENNReal.coe_toNNReal hT₀p.eLpNorm_ne_top]
        exact add_le_add_left (hC n) _

end Vitali

end TauCeti
