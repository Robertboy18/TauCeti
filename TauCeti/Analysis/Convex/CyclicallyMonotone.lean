/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.CTransform.CyclicalMonotonicity
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Pairing

/-!
# Cyclically monotone sets are subdifferentials of convex functions

Let `E` and `F` be real vector spaces paired by `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, written `⟪x, y⟫ = B x y`.
A set `Γ ⊆ E × F` is *cyclically monotone* when for all finitely many points `(x i, y i)` of `Γ`
and every permutation `σ`,

`∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫`.

Rockafellar's theorem says that these are exactly the subsets of the graph of the
subdifferential `∂f` of a proper lower-semicontinuous convex function `f : E → EReal`. This
file proves it, in the algebraic form valid on a bare dual pair: the potential is produced as a
Legendre–Fenchel conjugate `f = g⋆`, which is the algebraic description of a closed convex
function (every conjugate is convex and, for a topology compatible with the pairing, lower
semicontinuous; that every closed proper convex function is a conjugate is the Fenchel–Moreau
theorem, which needs a separation theorem and is not used here).

The proof is a translation. Cyclical monotonicity for the pairing is `c`-cyclical monotonicity
for the transport cost `c (x, y) = -⟪x, y⟫`, for which the `c`-transform vocabulary of optimal
transport is the Legendre–Fenchel vocabulary of convex analysis with the signs reversed
(`TauCeti.MeasureTheory.OptimalTransport.CTransform.Pairing`). The theorem of Rockafellar and
Rüschendorf for a general cost
(`TauCeti.IsCyclicallyMonotone.exists_isCConcave_subset_cSuperdifferential`) then specialises
to Rockafellar's original theorem.

## Main statements

* `TauCeti.isCyclicallyMonotone_pairingCost_subdifferential` — the graph of the subdifferential
  of any extended-real function is cyclically monotone;
* `TauCeti.IsCyclicallyMonotone.exists_fenchelConjugate_subset_subdifferential` —
  **Rockafellar's theorem**: a cyclically monotone set lies in the graph of the subdifferential
  of a Legendre–Fenchel conjugate, and
  `TauCeti.isCyclicallyMonotone_pairingCost_iff_exists_fenchelConjugate`, the resulting
  characterisation.

## References

* R. T. Rockafellar, *Characterization of the subdifferentials of convex functions*, Pacific J.
  Math. 17 (1966), 497--510, Theorem 1.
* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 24.8.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.27.
-/

public section

noncomputable section

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- The graph of the subdifferential of any extended-real function is cyclically monotone. -/
theorem isCyclicallyMonotone_pairingCost_subdifferential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (f : E → EReal) :
    IsCyclicallyMonotone (pairingCost B) {p | p.2 ∈ subdifferential B f p.1} := by
  simpa only [cSuperdifferential_pairingCost, neg_neg] using
    isCyclicallyMonotone_cSuperdifferential (pairingCost B) fun x => -f x

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {Γ : Set (E × F)}

/-- **Rockafellar's theorem.** A cyclically monotone set lies in the graph of the
subdifferential of a Legendre–Fenchel conjugate `g⋆`, hence of a convex function that is lower
semicontinuous for every topology compatible with the pairing, and is never `⊥` as soon as the
set is nonempty (`TauCeti.apply_ne_bot_of_mem_subdifferential`). -/
theorem IsCyclicallyMonotone.exists_fenchelConjugate_subset_subdifferential
    (hΓ : IsCyclicallyMonotone (pairingCost B) Γ) :
    ∃ g : F → EReal, Γ ⊆ {p | p.2 ∈ subdifferential B (fenchelConjugate B.flip g) p.1} := by
  obtain ⟨φ, hφ, hsub⟩ := hΓ.exists_isCConcave_subset_cSuperdifferential
  obtain ⟨g, hg⟩ := (isCConcave_pairingCost_iff B φ).1 hφ
  refine ⟨g, ?_⟩
  rwa [cSuperdifferential_pairingCost, hg] at hsub

/-- **Cyclically monotone sets are exactly the subsets of subdifferential graphs of closed
convex functions**, the latter described algebraically as Legendre–Fenchel conjugates. -/
theorem isCyclicallyMonotone_pairingCost_iff_exists_fenchelConjugate
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (Γ : Set (E × F)) :
    IsCyclicallyMonotone (pairingCost B) Γ ↔
      ∃ g : F → EReal, Γ ⊆ {p | p.2 ∈ subdifferential B (fenchelConjugate B.flip g) p.1} :=
  ⟨fun hΓ => hΓ.exists_fenchelConjugate_subset_subdifferential,
    fun ⟨_, h⟩ => (isCyclicallyMonotone_pairingCost_subdifferential B _).mono h⟩

end TauCeti

end

end
