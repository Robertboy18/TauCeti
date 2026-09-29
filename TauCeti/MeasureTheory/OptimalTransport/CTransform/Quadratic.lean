/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Rockafellar

/-!
# The quadratic cost and convex analysis

On a real inner product space `E`, the quadratic transport cost `c (x, y) = ‖x - y‖ ^ 2 / 2`
differs from the pairing cost `-⟪x, y⟫` by the split term `‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`. Split
terms are invisible to cyclical monotonicity and are absorbed by the `c`-transform vocabulary,
so the whole `c`-transform theory of the quadratic cost is the Legendre–Fenchel theory of the
inner product: a potential `φ` is `c`-concave exactly when `u = ‖·‖ ^ 2 / 2 - φ` is a
Legendre–Fenchel conjugate, its `c`-transform is `‖y‖ ^ 2 / 2 - u⋆ y`, its `c`-superdifferential
is the graph of the subdifferential `∂u`, and a set is `c`-cyclically monotone exactly when it is
cyclically monotone in the classical sense `∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫`. Rockafellar's
theorem then produces, from a `c`-cyclically monotone set, a conjugate `u` whose subdifferential
graph contains it. This is the algebraic step of Brenier's theorem: applied to the support of a
quadratic optimal plan, it yields the convex potential from which the Brenier map is later
extracted, once finite dimension, absolute continuity of the source and almost-everywhere
differentiability of `u` enter; none of these analytic and measure-theoretic hypotheses is used
here. Every bridge in this file accounts for the factor `1 / 2` in the cost.

## Main statements

* `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff` — `c`-cyclical monotonicity for the
  quadratic cost is cyclical monotonicity for the inner-product pairing, with
  `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le` its classical
  sum form;
* `TauCeti.cTransform_norm_sub_sq_div_two`, `TauCeti.cTransformSymm_norm_sub_sq_div_two`,
  `TauCeti.isCConcave_norm_sub_sq_div_two_iff` and
  `TauCeti.cSuperdifferential_norm_sub_sq_div_two` — the two `c`-transforms, `c`-concavity and
  the `c`-superdifferential for the quadratic cost in terms of the Legendre–Fenchel conjugate
  and the subdifferential of `‖·‖ ^ 2 / 2 - φ`;
* `TauCeti.IsCyclicallyMonotone.exists_fenchelConjugate_innerₗ_subset_subdifferential`
  — **Rockafellar's theorem for the quadratic cost**: a `c`-cyclically monotone set lies in the
  subdifferential graph of a Legendre–Fenchel conjugate for the inner product.

## References

* Y. Brenier, *Polar factorization and monotone rearrangement of vector-valued functions*, Comm.
  Pure Appl. Math. 44 (1991), 375--417.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1 and Theorem 2.12, where the quadratic cost is reduced to convex analysis.
-/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic cost is the inner-product pairing cost plus the split term
`‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`. -/
theorem norm_sub_sq_div_two_eq_pairingCost_add_add :
    (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) =
      fun p => pairingCost (innerₗ E) p + ‖p.1‖ ^ 2 / 2 + ‖p.2‖ ^ 2 / 2 := by
  funext p
  rw [pairingCost_apply, innerₗ_apply_apply, norm_sub_sq_real]
  ring

/-- `c`-cyclical monotonicity for the quadratic cost is cyclical monotonicity for the
inner-product pairing. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff {S : Set (E × E)} :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      IsCyclicallyMonotone (pairingCost (innerₗ E)) S := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    isCyclicallyMonotone_add_add_iff (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2)
      fun y => ‖y‖ ^ 2 / 2]

/-- `c`-cyclical monotonicity for the quadratic cost is the classical cyclical monotonicity
condition: rearranging the targets of finitely many points of the set does not increase the
total inner product. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le {S : Set (E × E)} :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      ∀ (n : ℕ) (x y : Fin n → E), (∀ i, (x i, y i) ∈ S) →
        ∀ σ : Equiv.Perm (Fin n), ∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫ := by
  rw [isCyclicallyMonotone_norm_sub_sq_div_two_iff, isCyclicallyMonotone_pairingCost_iff]
  simp only [innerₗ_apply_apply]

/-- The `c`-transform of a potential `φ` for the quadratic cost is `‖y‖ ^ 2 / 2 - u⋆ y`, where
`u = ‖·‖ ^ 2 / 2 - φ` and `u⋆` is its Legendre–Fenchel conjugate for the inner product. -/
theorem cTransform_norm_sub_sq_div_two (φ : E → EReal) (y : E) :
    cTransform (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) φ y =
      ((‖y‖ ^ 2 / 2 : ℝ) : EReal) -
        fenchelConjugate (innerₗ E) (fun x => ((‖x‖ ^ 2 / 2 : ℝ) : EReal) - φ x) y := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    cTransform_add_add (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2) (fun y => ‖y‖ ^ 2 / 2),
    cTransform_pairingCost, sub_eq_add_neg]
  simp only [EReal.neg_sub_coe]

/-- The symmetric `c`-transform of a potential `ψ` on the target for the quadratic cost is
`‖x‖ ^ 2 / 2 - v⋆ x`, where `v = ‖·‖ ^ 2 / 2 - ψ` and `v⋆` is its Legendre–Fenchel conjugate for
the inner product; the quadratic cost is symmetric, so the formula is the same as for the
infimal `c`-transform. -/
theorem cTransformSymm_norm_sub_sq_div_two (ψ : E → EReal) (x : E) :
    cTransformSymm (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) ψ x =
      ((‖x‖ ^ 2 / 2 : ℝ) : EReal) -
        fenchelConjugate (innerₗ E) (fun y => ((‖y‖ ^ 2 / 2 : ℝ) : EReal) - ψ y) x := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    cTransformSymm_add_add (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2) (fun y => ‖y‖ ^ 2 / 2),
    cTransformSymm_pairingCost, flip_innerₗ, sub_eq_add_neg]
  simp only [EReal.neg_sub_coe]

/-- A potential `φ` is `c`-concave for the quadratic cost exactly when `‖·‖ ^ 2 / 2 - φ` is a
Legendre–Fenchel conjugate for the inner product. -/
theorem isCConcave_norm_sub_sq_div_two_iff (φ : E → EReal) :
    IsCConcave (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) φ ↔
      ∃ g : E → EReal,
        (fun x => ((‖x‖ ^ 2 / 2 : ℝ) : EReal) - φ x) = fenchelConjugate (innerₗ E) g := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    isCConcave_add_add_iff (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2) (fun y => ‖y‖ ^ 2 / 2),
    isCConcave_pairingCost_iff, flip_innerₗ]
  simp only [EReal.neg_sub_coe]

/-- The `c`-superdifferential of a potential `φ` for the quadratic cost is the graph of the
subdifferential of `‖·‖ ^ 2 / 2 - φ` for the inner product. -/
theorem cSuperdifferential_norm_sub_sq_div_two (φ : E → EReal) :
    cSuperdifferential (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) φ =
      {p | p.2 ∈ subdifferential (innerₗ E) (fun x => ((‖x‖ ^ 2 / 2 : ℝ) : EReal) - φ x) p.1} := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    cSuperdifferential_add_add (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2)
      (fun y => ‖y‖ ^ 2 / 2),
    cSuperdifferential_pairingCost]
  simp only [EReal.neg_sub_coe]

/-- The subdifferential graph of any extended-real function on `E` is `c`-cyclically monotone
for the quadratic cost. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_subdifferential (u : E → EReal) :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2)
      {p | p.2 ∈ subdifferential (innerₗ E) u p.1} :=
  isCyclicallyMonotone_norm_sub_sq_div_two_iff.2
    (isCyclicallyMonotone_pairingCost_subdifferential (innerₗ E) u)

/-- **Rockafellar's theorem for the quadratic cost.** A `c`-cyclically monotone set for the cost
`‖x - y‖ ^ 2 / 2` lies in the subdifferential graph of a Legendre–Fenchel conjugate `u = g⋆` for
the inner product: `y ∈ ∂u(x)` for every `(x, y)` in the set. -/
theorem IsCyclicallyMonotone.exists_fenchelConjugate_innerₗ_subset_subdifferential
    {S : Set (E × E)} (hS : IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S) :
    ∃ g : E → EReal,
      S ⊆ {p | p.2 ∈ subdifferential (innerₗ E) (fenchelConjugate (innerₗ E) g) p.1} := by
  have hS' := isCyclicallyMonotone_norm_sub_sq_div_two_iff.1 hS
  obtain ⟨g, hg⟩ := hS'.exists_fenchelConjugate_subset_subdifferential
  rw [flip_innerₗ] at hg
  exact ⟨g, hg⟩

/-- **`c`-cyclically monotone sets for the quadratic cost are exactly the subsets of
subdifferential graphs of closed convex functions**, the latter described algebraically as
Legendre–Fenchel conjugates for the inner product. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff_exists_fenchelConjugate (S : Set (E × E)) :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      ∃ g : E → EReal,
        S ⊆ {p | p.2 ∈ subdifferential (innerₗ E) (fenchelConjugate (innerₗ E) g) p.1} :=
  ⟨fun hS => hS.exists_fenchelConjugate_innerₗ_subset_subdifferential,
    fun ⟨_, h⟩ => (isCyclicallyMonotone_norm_sub_sq_div_two_subdifferential _).mono h⟩

end TauCeti

end

end
