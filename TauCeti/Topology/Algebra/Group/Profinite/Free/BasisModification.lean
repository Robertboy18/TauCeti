/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Deviation
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Graded

/-!
# Basis modifications of a free pro-`p` group and the maps `δ`

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with
canonical generators `x_i = freeProP.of i`, and let `λ_k = λ_k(F)` be its lower `p`-series. A
family `w : X → λ_m(F)` defines the **basis modification** `θ_w : F → F`, `x_i ↦ x_i * w_i`
(`TauCeti.freeProP.basisModification`). It is congruent to the identity modulo `λ_m`, so for a
relator `r ∈ λ_1(F)` it moves `r` inside its coset by the element `r⁻¹ * θ_w r ∈ λ_{m+1}(F)`,
whose class in `gr_{m+1}(F)` is the graded deviation `D_1 r̄` of `θ_w`
(`TauCeti.gradedDeviation`).

For `m ≥ 1` that class is given by the **basis-modification map**
`δ = TauCeti.freeProP.basisModificationDelta`: writing `r̄ ∈ gr_1(F)` in the standard basis
`TauCeti.freeProP.degreeOneBasis` as `r̄ = Σ_i c_i π x̄_i + Σ_{i<k} a_{ik} [x̄_i, x̄_k]`, the class
of `r⁻¹ * θ_w r` in `gr_{m+1}(F)` is

  `δ(w̄) = Σ_i c_i (π w̄_i + (p choose 2) • [w̄_i, x̄_i])
          + Σ_{i<k} a_{ik} ([w̄_i, x̄_k] - [w̄_k, x̄_i])`,

an `𝔽_p`-linear function of the classes `w̄_i ∈ gr_m(F)` alone. The bracket part is the
derivative of the commutator part of `r̄` in the direction `w̄`, and for odd `p` the `p`-power
part contributes `Σ_i c_i π w̄_i`. For `p = 2` the `p`-power part contributes in addition the
brackets `Σ_i c_i [w̄_i, x̄_i]`: the square of `x_i * w_i` is `x_i ^ 2 * w_i ^ 2 * ⁅w_i, x_i⁆` up
to `λ_{m+2}(F)`, and the commutator `⁅w_i, x_i⁆` lies in `λ_{m+1}(F)` and not in `λ_{m+2}(F)`.
That term is the trace, in every degree, of the failure of additivity of `π` on `gr_0(F)` at
`p = 2`.

The image of `δ` is the subspace of `gr_{m+1}(F)` that the successive-approximation arguments of
the classification of Demushkin groups compare with `gr_{m+1}(F)`; there `m + 1` is the modulus of
the normal-form congruence, and the classes `w̄_i` are the level-`m` basis corrections.

## Main definitions

* `TauCeti.freeProP.basisModification`: the endomorphism `θ_w : F → F`, `x_i ↦ x_i * w_i`.
* `TauCeti.freeProP.basisModificationDelta`: for `r̄ ∈ gr_1(F)` and `m ≥ 1`, the `𝔽_p`-linear map
  `δ : gr_m(F)^X → gr_{m+1}(F)`.

## Main results

* `TauCeti.freeProP.inv_mul_basisModification_mem`: `θ_w` is congruent to the identity modulo
  `λ_m(F)`.
* `TauCeti.freeProP.gradedDeviation_basisModification`,
  `TauCeti.freeProP.gradedMk_inv_mul_basisModification`: the class of `r⁻¹ * θ_w r` in
  `gr_{m+1}(F)` is `δ(w̄)`; in particular it depends only on the classes `w̄_i`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5.
-/

public section

namespace TauCeti.freeProP

open Subgroup
open scoped commutatorElement

universe u

variable {p : ℕ} {X : Type u} {m : ℕ}

/-! ### The basis modification `x_i ↦ x_i * w_i` -/

/-- **The basis modification** `θ_w : F → F`, `x_i ↦ x_i * w_i`, of the free pro-`p` group
`F = freeProP p X` by a family `w : X → λ_m(F)`. It is congruent to the identity modulo `λ_m(F)`
(`TauCeti.freeProP.inv_mul_basisModification_mem`). -/
noncomputable def basisModification (w : X → pLowerCentralSeries p (freeProP p X) m) :
    freeProP p X →ₜ* freeProP p X :=
  lift (isProP_freeProP p X) fun i ↦ of i * (w i : freeProP p X)

@[simp]
theorem basisModification_of (w : X → pLowerCentralSeries p (freeProP p X) m) (i : X) :
    basisModification w (of i) = of i * (w i : freeProP p X) :=
  lift_of _ _ i

/-- **The basis modification is congruent to the identity modulo `λ_m(F)`**: the elements on
which it agrees with the identity modulo `λ_m(F)` form a closed subgroup containing the
generators. -/
theorem inv_mul_basisModification_mem (w : X → pLowerCentralSeries p (freeProP p X) m)
    (g : freeProP p X) :
    g⁻¹ * basisModification w g ∈ pLowerCentralSeries p (freeProP p X) m := by
  have hN : IsClosed ((pLowerCentralSeries p (freeProP p X) m : Subgroup (freeProP p X)) :
      Set (freeProP p X)) :=
    isClosed_pLowerCentralSeries m
  -- `K` is the closed subgroup on which `θ_w` agrees with the identity modulo `λ_m(F)`.
  let K : Subgroup (freeProP p X) :=
    (QuotientGroup.mk' (pLowerCentralSeries p (freeProP p X) m)).eqLocus
      ((QuotientGroup.mk' _).comp (basisModification w).toMonoidHom)
  have hmem : ∀ x, x ∈ K ↔
      ((x : freeProP p X) : freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) m) =
        basisModification w x :=
    fun x ↦ Iff.rfl
  have hKc : IsClosed (K : Set (freeProP p X)) :=
    isClosed_eq QuotientGroup.continuous_mk
      (QuotientGroup.continuous_mk.comp (basisModification w).continuous)
  have hle : (Subgroup.closure (Set.range (of : X → freeProP p X))).topologicalClosure ≤ K := by
    refine topologicalClosure_minimal _ ((Subgroup.closure_le _).mpr ?_) hKc
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hmem, basisModification_of, QuotientGroup.mk_mul_of_mem _ (w i).2]
  rw [topologicalClosure_closure_range_of_eq_top] at hle
  exact QuotientGroup.eq.mp ((hmem g).mp (hle (Subgroup.mem_top g)))

/-- **The deviation of the basis modification on a generator class** is the class of the
modification: `D_0 x̄_i = w̄_i` in `gr_m(F)`. -/
theorem gradedDeviation_basisModification_gradedMkZero_of
    (w : X → pLowerCentralSeries p (freeProP p X) m) (i : X) :
    gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
        (inv_mul_basisModification_mem w) 0 (gradedMkZero p (freeProP p X) (of i)) =
      gradedMk p (freeProP p X) m (w i) := by
  rw [gradedDeviation_gradedMkZero]
  congr 1
  exact Subtype.ext (by simp)

/-! ### The maps `δ` -/

/-- The bracket with a fixed degree-zero class on the right, `v ↦ [v, z]`, as an `𝔽_p`-linear map
`gr_m(F) → gr_{m+1}(F)`. -/
private noncomputable def bracketLinear (z : gradedPiece p (freeProP p X) 0) :
    gradedPiece p (freeProP p X) m →ₗ[ZMod p] gradedPiece p (freeProP p X) (m + 1) :=
  ((gradedBracket p (freeProP p X) m 0).flip z).toZModLinearMap p

private theorem bracketLinear_apply (z : gradedPiece p (freeProP p X) 0)
    (v : gradedPiece p (freeProP p X) m) :
    bracketLinear z v = gradedBracket p (freeProP p X) m 0 v z :=
  rfl

section Delta

variable [Fact p.Prime] [Fintype X] [LinearOrder X]

variable (p X) in
/-- **The basis-modification map `δ`** of a class `ρ ∈ gr_1(F)`, for `m ≥ 1`: the `𝔽_p`-linear
map `gr_m(F)^X → gr_{m+1}(F)`,

  `δ(v) = Σ_i c_i (π v_i + (p choose 2) • [v_i, x̄_i]) + Σ_{i<k} a_{ik} ([v_i, x̄_k] - [v_k, x̄_i])`

where `c_i` and `a_{ik}` are the coordinates of `ρ` in the standard basis
`TauCeti.freeProP.degreeOneBasis` of `gr_1(F)`, that is
`ρ = Σ_i c_i π x̄_i + Σ_{i<k} a_{ik} [x̄_i, x̄_k]`. For a relator `r ∈ λ_1(F)` with class `ρ`, and
`w : X → λ_m(F)` with classes `v_i = w̄_i`, `δ(v)` is the class in `gr_{m+1}(F)` of `r⁻¹ * θ_w r`,
the amount by which the basis modification `θ_w` moves `r`
(`TauCeti.freeProP.gradedMk_inv_mul_basisModification`). Its value is
`TauCeti.freeProP.basisModificationDelta_apply`. -/
noncomputable def basisModificationDelta (hm : 1 ≤ m) (ρ : gradedPiece p (freeProP p X) 1) :
    (X → gradedPiece p (freeProP p X) m) →ₗ[ZMod p] gradedPiece p (freeProP p X) (m + 1) :=
  ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) •
      (((gradedPowAddMonoidHom p (freeProP p X) hm).toZModLinearMap p +
        p.choose 2 • bracketLinear (gradedMkZero p (freeProP p X) (of i))) ∘ₗ
          LinearMap.proj i) +
    ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
      (bracketLinear (gradedMkZero p (freeProP p X) (of ij.1.2)) ∘ₗ LinearMap.proj ij.1.1 -
        bracketLinear (gradedMkZero p (freeProP p X) (of ij.1.1)) ∘ₗ LinearMap.proj ij.1.2)

/-- **The value of `δ`**: with `ρ = Σ_i c_i π x̄_i + Σ_{i<k} a_{ik} [x̄_i, x̄_k]`,
`δ(v) = Σ_i c_i (π v_i + (p choose 2) • [v_i, x̄_i]) + Σ_{i<k} a_{ik} ([v_i, x̄_k] - [v_k, x̄_i])`.
-/
theorem basisModificationDelta_apply (hm : 1 ≤ m) (ρ : gradedPiece p (freeProP p X) 1)
    (v : X → gradedPiece p (freeProP p X) m) :
    basisModificationDelta p X hm ρ v =
      ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) •
          (gradedPow p (freeProP p X) m (v i) +
            p.choose 2 • gradedBracket p (freeProP p X) m 0 (v i)
              (gradedMkZero p (freeProP p X) (of i))) +
        ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
          (gradedBracket p (freeProP p X) m 0 (v ij.1.1)
              (gradedMkZero p (freeProP p X) (of ij.1.2)) -
            gradedBracket p (freeProP p X) m 0 (v ij.1.2)
              (gradedMkZero p (freeProP p X) (of ij.1.1))) := by
  simp only [basisModificationDelta, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sub_apply,
    AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply, bracketLinear_apply]

/-- **The class of the moved relator is `δ(w̄)`.** For `m ≥ 1`, `w : X → λ_m(F)` and
`ρ ∈ gr_1(F)`, the graded deviation of the basis modification `θ_w` on `ρ` is `δ_ρ(w̄)`, where
`w̄_i ∈ gr_m(F)` is the class of `w_i`. Both sides are linear in `ρ`, and they agree on the
standard basis of `gr_1(F)` by the Leibniz rule and the `π`-compatibility of the deviation. -/
theorem gradedDeviation_basisModification (hm : 1 ≤ m)
    (w : X → pLowerCentralSeries p (freeProP p X) m) (ρ : gradedPiece p (freeProP p X) 1) :
    gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
        (inv_mul_basisModification_mem w) 1 ρ =
      basisModificationDelta p X hm ρ fun i ↦ gradedMk p (freeProP p X) m (w i) := by
  set v : X ⊕ {ij : X × X // ij.1 < ij.2} → gradedPiece p (freeProP p X) (m + 1) :=
    Sum.elim
      (fun i ↦ gradedPow p (freeProP p X) m (gradedMk p (freeProP p X) m (w i)) +
        p.choose 2 • gradedBracket p (freeProP p X) m 0 (gradedMk p (freeProP p X) m (w i))
          (gradedMkZero p (freeProP p X) (of i)))
      fun ij ↦ gradedBracket p (freeProP p X) m 0 (gradedMk p (freeProP p X) m (w ij.1.1))
          (gradedMkZero p (freeProP p X) (of ij.1.2)) -
        gradedBracket p (freeProP p X) m 0 (gradedMk p (freeProP p X) m (w ij.1.2))
          (gradedMkZero p (freeProP p X) (of ij.1.1)) with hv
  have key : (gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
      (inv_mul_basisModification_mem w) 1).toZModLinearMap p =
        (degreeOneBasis p X).constr (ZMod p) v := by
    refine (degreeOneBasis p X).ext fun b ↦ ?_
    rw [Module.Basis.constr_basis, AddMonoidHom.coe_toZModLinearMap, degreeOneBasis_apply]
    rcases b with i | ij
    · rw [degreeOneFamily_inl, gradedDeviation_gradedPow_zero,
        gradedDeviation_basisModification_gradedMkZero_of]
      rfl
    · rw [degreeOneFamily_inr, gradedDeviation_gradedBracket_zero _ _ _ hm,
        gradedDeviation_basisModification_gradedMkZero_of,
        gradedDeviation_basisModification_gradedMkZero_of]
      rfl
  have h := LinearMap.congr_fun key ρ
  rw [AddMonoidHom.coe_toZModLinearMap, Module.Basis.constr_apply_fintype,
    Fintype.sum_sum_type] at h
  rw [h, basisModificationDelta_apply]
  simp only [Module.Basis.equivFun_apply, hv, Sum.elim_inl, Sum.elim_inr]

/-- **The basis modification `θ_w` moves a relator `r ∈ λ_1(F)` by `δ_r̄(w̄)`**: the class in
`gr_{m+1}(F)` of `r⁻¹ * θ_w r` is `δ_r̄(w̄)`, for `m ≥ 1`. In particular that class depends only
on the classes `w̄_i ∈ gr_m(F)` of the modifications. -/
theorem gradedMk_inv_mul_basisModification (hm : 1 ≤ m)
    (w : X → pLowerCentralSeries p (freeProP p X) m)
    (r : pLowerCentralSeries p (freeProP p X) 1) :
    gradedMk p (freeProP p X) (m + 1) ⟨(r : freeProP p X)⁻¹ * basisModification w r,
        inv_mul_apply_mem_pLowerCentralSeries (basisModification w).toMonoidHom
          (basisModification w).continuous (inv_mul_basisModification_mem w) r.2⟩ =
      basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)
        fun i ↦ gradedMk p (freeProP p X) m (w i) := by
  have h := gradedDeviation_basisModification hm w (gradedMk p (freeProP p X) 1 r)
  rwa [gradedDeviation_gradedMk] at h

end Delta

end TauCeti.freeProP
