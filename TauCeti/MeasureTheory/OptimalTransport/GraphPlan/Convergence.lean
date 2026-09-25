/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import TauCeti.MeasureTheory.Function.Lusin
public import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Convergence of transport maps and of their graph plans

Fix a probability measure `μ` on `X`, and let `T n, T₀ : X → Y` be almost-everywhere measurable
maps into a second-countable pseudo-emetric space. Their graph plans `TauCeti.graphPlan (T n) μ`
are probability measures on `X × Y`, and the question is how the convergence of the plans is
related to the convergence of the maps. The answer is the following pair of theorems, which
turn statements about deterministic transport plans into statements about the maps inducing them
and back.

**Narrow convergence is convergence in measure.** The graph plans of `T n` converge weakly to
the graph plan of `T₀` exactly when `T n` converges to `T₀` in `μ`-measure. From convergence in
measure, a subsequence converges almost everywhere, and almost-everywhere convergence gives the
convergence in distribution of the graph maps along it; the full sequence follows because every
subsequence has such a further subsequence. Conversely, Lusin's theorem makes `T₀` continuous on
a closed set `F` of nearly full measure, so that `{(x, y) | x ∈ F, ε ≤ edist y (T₀ x)}` is a
closed subset of `X × Y` carrying no mass under the limit graph plan; the portmanteau theorem
bounds the mass the plans of `T n` give it, and that mass is exactly
`μ {x ∈ F | ε ≤ edist (T n x) (T₀ x)}`.

**`Lᵖ` convergence is convergence in measure plus uniform integrability.** For `1 ≤ p < ∞` and
maps with finite `p`-th moment about a basepoint `y₀`, the distances `dist (T n x) (T₀ x)`
converge to `0` in `Lᵖ(μ)` exactly when `T n` converges to `T₀` in measure and the family
`dist (T n ·) y₀` is uniformly integrable in `Lᵖ(μ)`. This is Vitali's convergence theorem
transported to metric-space-valued maps; the uniform integrability condition does not depend on
the basepoint, since the left-hand side does not mention it. Uniform integrability is Mathlib's
`MeasureTheory.UnifIntegrable`, the predicate its Vitali theorem uses, or equivalently
`MeasureTheory.UniformIntegrable`, which adds a uniform `Lᵖ` bound; the bound follows from the
`Lᵖ` convergence, since a convergent sequence of finite norms is bounded.

The weak topology on `ProbabilityMeasure (X × Y)` is the one Mathlib puts on probability measures,
and graph plans are bundled through `MeasureTheory.ProbabilityMeasure.map` along `x ↦ (x, T x)`,
whose underlying measure is `TauCeti.graphPlan` by `TauCeti.toMeasure_map_prodMk_self`.

## Main statements

* `TauCeti.tendsto_map_prodMk_self_iff_tendstoInMeasure` — the graph plans of `T n` converge
  weakly to the graph plan of `T₀` if and only if `T n` converges to `T₀` in `μ`-measure; the two
  implications are `TauCeti.tendsto_map_prodMk_self_of_tendstoInMeasure`, valid on any
  topological source, and `TauCeti.tendstoInMeasure_of_tendsto_map_prodMk_self`, which needs a
  pseudo-metrizable Borel source for Lusin's theorem;
* `TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable` — **Vitali's theorem
  for maps into a pseudometric space**: for `1 ≤ p < ∞`, `Lᵖ` convergence of `dist (T n ·) (T₀ ·)`
  to `0` is convergence in measure together with uniform integrability of `dist (T n ·) y₀`;
* `TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_uniformIntegrable` — the same with
  `MeasureTheory.UniformIntegrable`, which also records the uniform `Lᵖ` bound.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, second edition, Birkhäuser 2008, Lemma 5.4.1, the equivalence between
  narrow convergence of graph plans and convergence in measure, and the `Lᵖ` refinement that
  follows it.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

section Narrow

variable {μ : ProbabilityMeasure X} {T : ℕ → X → Y} {T₀ : X → Y}

section OfTendstoInMeasure

variable [TopologicalSpace X] [OpensMeasurableSpace X] [PseudoEMetricSpace Y]
  [OpensMeasurableSpace Y] [SecondCountableTopologyEither X Y]

/-- If the maps `T n` converge to `T₀` in `μ`-measure, then their graph plans converge weakly to
the graph plan of `T₀`. -/
theorem tendsto_map_prodMk_self_of_tendstoInMeasure (hT : ∀ n, AEMeasurable (T n) μ)
    (hT₀ : AEMeasurable T₀ μ) (h : TendstoInMeasure (μ : Measure X) T atTop T₀) :
    Tendsto (fun n ↦ μ.map fun x ↦ (x, T n x)) atTop (𝓝 (μ.map fun x ↦ (x, T₀ x))) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, -, hms⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε ↦ (h ε hε).comp hns
  exact ⟨ms, (tendstoInDistribution_of_ae_tendsto (fun k ↦ aemeasurable_prodMk_self (hT _))
    (aemeasurable_prodMk_self hT₀) (hms.mono fun x hx ↦ tendsto_const_nhds.prodMk_nhds hx)).tendsto⟩

end OfTendstoInMeasure

variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]
  [PseudoEMetricSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]

/-- If the graph plans of `T n` converge weakly to the graph plan of `T₀`, then `T n` converges
to `T₀` in `μ`-measure. -/
theorem tendstoInMeasure_of_tendsto_map_prodMk_self (hT : ∀ n, AEMeasurable (T n) μ)
    (hT₀ : AEMeasurable T₀ μ)
    (h : Tendsto (fun n ↦ μ.map fun x ↦ (x, T n x)) atTop (𝓝 (μ.map fun x ↦ (x, T₀ x)))) :
    TendstoInMeasure (μ : Measure X) T atTop T₀ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨F, -, hF, hFμ, hFcont⟩ := exists_isClosed_measure_diff_lt_continuousOn_of_aemeasurable
    (μ := (μ : Measure X)) hT₀ MeasurableSet.univ (measure_ne_top _ _) hδ2.ne'
  rw [← compl_eq_univ_sdiff] at hFμ
  set C : Set (X × Y) := F ×ˢ univ ∩ {z | ε ≤ edist z.2 (T₀ z.1)} with hC
  have hCclosed : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed (t := Ici ε) ?_ (hF.prod isClosed_univ)
      isClosed_Ici
    exact continuous_edist.comp_continuousOn
      (continuous_snd.continuousOn.prodMk (hFcont.comp continuous_fst.continuousOn fun z hz ↦ hz.1))
  have hCmeas : MeasurableSet C := hCclosed.measurableSet
  have hlim : ((μ.map fun x ↦ (x, T₀ x) : ProbabilityMeasure (X × Y)) : Measure (X × Y)) C = 0 := by
    have hempty : {x | (x, T₀ x) ∈ C} = ∅ := by ext x; simp [hC, hε.ne']
    rw [toMeasure_map_prodMk_self, graphPlan_apply hT₀ hCmeas, hempty, measure_empty]
  have hCn : Tendsto
      (fun n ↦ ((μ.map fun x ↦ (x, T n x) : ProbabilityMeasure (X × Y)) : Measure (X × Y)) C)
      atTop (𝓝 0) := by
    refine tendsto_of_le_liminf_of_limsup_le zero_le ?_
    rw [← hlim]
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hCclosed
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hCn (δ / 2) hδ2] with n hn
  rw [toMeasure_map_prodMk_self, graphPlan_apply (hT n) hCmeas] at hn
  calc (μ : Measure X) {x | ε ≤ edist (T n x) (T₀ x)}
      ≤ (μ : Measure X) ({x | (x, T n x) ∈ C} ∪ Fᶜ) := by
        refine measure_mono fun x hx ↦ ?_
        by_cases hxF : x ∈ F
        · exact Or.inl ⟨⟨hxF, mem_univ _⟩, hx⟩
        · exact Or.inr hxF
    _ ≤ (μ : Measure X) {x | (x, T n x) ∈ C} + (μ : Measure X) Fᶜ := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hn hFμ.le
    _ = δ := ENNReal.add_halves δ

/-- **Narrow convergence of graph plans is convergence in measure.** For a probability measure
`μ` on a pseudo-metrizable Borel space and almost-everywhere measurable maps into a
second-countable pseudo-emetric space, the graph plans of `T n` converge weakly to the graph plan
of `T₀` if and only if `T n` converges to `T₀` in `μ`-measure. -/
theorem tendsto_map_prodMk_self_iff_tendstoInMeasure (hT : ∀ n, AEMeasurable (T n) μ)
    (hT₀ : AEMeasurable T₀ μ) :
    Tendsto (fun n ↦ μ.map fun x ↦ (x, T n x)) atTop (𝓝 (μ.map fun x ↦ (x, T₀ x))) ↔
      TendstoInMeasure (μ : Measure X) T atTop T₀ :=
  ⟨tendstoInMeasure_of_tendsto_map_prodMk_self hT hT₀,
    tendsto_map_prodMk_self_of_tendstoInMeasure hT hT₀⟩

end Narrow

section Lp

variable [PseudoMetricSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
  {μ : Measure X} [IsFiniteMeasure μ] {T : ℕ → X → Y} {T₀ : X → Y} {y₀ : Y} {p : ℝ≥0∞}

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
  have hd : ∀ n, AEStronglyMeasurable (fun x ↦ dist (T n x) (T₀ x)) μ := fun n ↦
    ((hT n).dist hT₀).aestronglyMeasurable
  -- convergence in measure of the maps is convergence in measure of their distances to `0`
  have key : TendstoInMeasure μ T atTop T₀ ↔
      TendstoInMeasure μ (fun n x ↦ dist (T n x) (T₀ x)) atTop 0 := by
    simp only [tendstoInMeasure_iff_dist, Pi.zero_apply, Real.dist_0_eq_abs, abs_dist]
  -- the two triangle inequalities, in the form `UnifIntegrable.ae_mono` and `MemLp.of_le` take
  have h₁ : ∀ n, ∀ᵐ x ∂μ, ‖dist (T n x) (T₀ x)‖ ≤ ‖dist (T n x) y₀ + dist (T₀ x) y₀‖ :=
    fun n ↦ ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
      exact dist_triangle_right _ _ _
  have h₂ : ∀ n, ∀ᵐ x ∂μ, ‖dist (T n x) y₀‖ ≤ ‖dist (T n x) (T₀ x) + dist (T₀ x) y₀‖ :=
    fun n ↦ ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
      exact dist_triangle _ _ _
  have hdp : ∀ n, MemLp (fun x ↦ dist (T n x) (T₀ x)) p μ := fun n ↦
    ((hTp n).add hT₀p).of_le (hd n) (h₁ n)
  have hd₀ : UnifIntegrable (fun _ : ℕ ↦ fun x ↦ dist (T₀ x) y₀) p μ :=
    unifIntegrable_const hp hp' hT₀p
  -- Vitali's theorem for the distances, then transport of uniform integrability
  have hV := tendstoInMeasure_iff_tendsto_Lp_finite hp hp' hdp (MemLp.zero (p := p) (μ := μ))
  simp only [sub_zero] at hV
  rw [← hV, key]
  refine and_congr_right fun _ ↦ ⟨fun hui ↦ ?_, fun hui ↦ ?_⟩
  · exact (UnifIntegrable.add hui hd₀ hp hd fun _ ↦ hT₀p.aestronglyMeasurable).ae_mono
      fun n ↦ (h₂ n).mono fun x hx ↦ enorm_le_iff_norm_le.2 hx
  · exact (UnifIntegrable.add hui hd₀ hp (fun n ↦ (hTp n).aestronglyMeasurable)
      fun _ ↦ hT₀p.aestronglyMeasurable).ae_mono fun n ↦ (h₁ n).mono fun x hx ↦
        enorm_le_iff_norm_le.2 hx

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
  -- the convergent sequence of finite `Lᵖ` norms of the distances is bounded
  have hd : ∀ n, AEStronglyMeasurable (fun x ↦ dist (T n x) (T₀ x)) μ := fun n ↦
    ((hT n).dist hT₀).aestronglyMeasurable
  have hfin : ∀ n, eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ ≠ ∞ := fun n ↦
    (((hTp n).add hT₀p).of_le (hd n) (ae_of_all _ fun x ↦ by
      rw [Pi.add_apply, Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
      exact dist_triangle_right _ _ _)).eLpNorm_ne_top
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ n, eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ ≤ C := by
    have ht : Tendsto (fun n ↦ (eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ).toNNReal) atTop
        (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp hL
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    exact ⟨C, fun n ↦ by
      rw [← ENNReal.coe_toNNReal (hfin n)]
      exact ENNReal.coe_le_coe.2 (hC ⟨n, rfl⟩)⟩
  refine ⟨C + (eLpNorm (fun x ↦ dist (T₀ x) y₀) p μ).toNNReal, fun n ↦ ?_⟩
  calc eLpNorm (fun x ↦ dist (T n x) y₀) p μ
      ≤ eLpNorm ((fun x ↦ dist (T n x) (T₀ x)) + fun x ↦ dist (T₀ x) y₀) p μ :=
        eLpNorm_mono_ae <| ae_of_all _ fun x ↦ by
          rw [Pi.add_apply, Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
          exact dist_triangle _ _ _
    _ ≤ eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ + eLpNorm (fun x ↦ dist (T₀ x) y₀) p μ :=
        eLpNorm_add_le (hd n) hT₀p.aestronglyMeasurable hp
    _ ≤ C + (eLpNorm (fun x ↦ dist (T₀ x) y₀) p μ).toNNReal := by
        rw [ENNReal.coe_toNNReal hT₀p.eLpNorm_ne_top]
        exact add_le_add_left (hC n) _

end Lp

end TauCeti
