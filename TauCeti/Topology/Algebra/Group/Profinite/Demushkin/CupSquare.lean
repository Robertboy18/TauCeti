/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.CharacterLift
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ZModFourLift
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.RankParity
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The cup squares of a Demushkin group at `p = 2` vanish exactly when `q ≠ 2`

Let `G` be a Demushkin group at `p = 2`. The cup square of a class of `H¹(G, 𝔽₂)` vanishes exactly
when the corresponding character `G → 𝔽₂` lifts to a continuous character `G → ℤ/4`
(`TauCeti.cupFp_self_eq_zero_iff_exists_zmodFourReductionClass_eq`, the Bockstein description of
the cup square). Characters with values in `𝔽₂` or `ℤ/4` factor through the topological
abelianization `G^{ab} ≅ ℤ_2^{n-1} × ℤ_2 ⧸ (q)`, where `q = q(G)` is Labute's invariant, so the
question becomes one about this abelian pro-`2` group. If `q ≠ 2`, then `4 ∣ q`, including
`q = 0`, and every character lifts, so every cup square vanishes: the cup form is alternating. If
`q = 2`, the projection onto the torsion factor `ℤ_2 ⧸ (2) = 𝔽₂` does not lift, because an element
of order two cannot map to an odd element of `ℤ/4`, so some cup square is nonzero: the cup form is
symmetric but not alternating.

This is the invariant-theoretic content of the trichotomy in Labute's classification: the cup
form of a Demushkin group is alternating exactly when `q ≠ 2`, at every prime, since for odd `p`
every cup square vanishes by graded commutativity. It decides which of Labute's normal forms the
relator of `G` can be brought to: the alternating form `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` when
`q ≠ 2`, and the dyadic forms with a square `x₁²` when `q = 2`. In particular a Demushkin group at
`p = 2` with `q ≠ 2` has even rank, and one of odd rank has `q = 2`.

## Main results

* `TauCeti.IsDemushkin.forall_exists_zmodFourReduction_eq_iff_demushkinQ_ne_two`: every continuous
  character `G → 𝔽₂` of a Demushkin group at `p = 2` lifts to `ℤ/4` exactly when `q(G) ≠ 2`.
* `TauCeti.IsDemushkin.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two`: **every cup square on
  `H¹(G, 𝔽₂)` vanishes exactly when `q(G) ≠ 2`.**
* `TauCeti.IsDemushkin.exists_cupFp_self_ne_zero_iff_demushkinQ_eq_two`: some cup square is
  nonzero exactly when `q(G) = 2`.
* `TauCeti.IsDemushkin.even_demushkinRank_of_demushkinQ_ne_two`,
  `TauCeti.IsDemushkin.demushkinQ_eq_two_of_odd_demushkinRank`: at `p = 2`, `q(G) ≠ 2` forces the
  rank to be even, and an odd rank forces `q(G) = 2`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1
  and §3.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter III, §9.
-/

public section

namespace TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Transport of lifting problems along the abelianization -/

/-- **Lifting characters from `𝔽₂` to `ℤ/4` is decided on the abelianization.** For a model
`A ≅ G^{ab}` of the topological abelianization of `G`, every continuous character `G → 𝔽₂` lifts
to a continuous character `G → ℤ/4` exactly when every continuous character `A → 𝔽₂` does: both
kinds of characters factor through `G^{ab}`. -/
theorem forall_exists_zmodFourReduction_eq_iff_of_topologicalAbelianization
    {A : Type*} [Group A] [TopologicalSpace A] (e : TopologicalAbelianization G ≃ₜ* A) :
    (∀ χ : continuousZModDual 2 G, ∃ φ : G →ₜ* Multiplicative (ZMod 4),
        φ.zmodFourReduction = χ) ↔
      ∀ χ : A →ₜ* Multiplicative (ZMod 2), ∃ φ : A →ₜ* Multiplicative (ZMod 4),
        ∀ a, ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ a)) =
          Multiplicative.toAdd (χ a) := by
  -- The projection `G → G^{ab} ≅ A`, kept opaque so that rewriting does not unfold it.
  obtain ⟨π, hπ_apply⟩ : ∃ π : G →ₜ* A, ∀ g, π g = e (g : TopologicalAbelianization G) :=
    ⟨(e : TopologicalAbelianization G →ₜ* A).comp
      (ContinuousMonoidHom.quotientMk (commutator G).topologicalClosure), fun g ↦ rfl⟩
  have hsurj : Function.Surjective π := fun a ↦ by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm a)
    exact ⟨g, by rw [hπ_apply, hg, ContinuousMulEquiv.apply_symm_apply]⟩
  refine ⟨fun h χ ↦ ?_, fun h χ ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := h (Additive.ofMul (χ.comp π))
    rw [φ.zmodFourReduction_eq_iff] at hφ
    refine ⟨(TopologicalAbelianization.lift φ).comp (e.symm : A →ₜ* TopologicalAbelianization G),
      fun a ↦ ?_⟩
    obtain ⟨g, rfl⟩ := hsurj a
    rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, hπ_apply,
      ContinuousMonoidHom.coe_coe, ContinuousMulEquiv.symm_apply_apply,
      TopologicalAbelianization.lift_mk, hφ g, toMul_ofMul, ContinuousMonoidHom.coe_comp,
      Function.comp_apply, hπ_apply]
  · obtain ⟨χ', rfl⟩ : ∃ χ' : G →ₜ* Multiplicative (ZMod 2), Additive.ofMul χ' = χ :=
      ⟨Additive.toMul χ, rfl⟩
    obtain ⟨φ, hφ⟩ := h ((TopologicalAbelianization.lift χ').comp
      (e.symm : A →ₜ* TopologicalAbelianization G))
    refine ⟨φ.comp π, (φ.comp π).zmodFourReduction_eq_iff _ |>.2 fun g ↦ ?_⟩
    -- The two sides are compared up to definitional unfolding of `comp` and of the coercions,
    -- because the monoid instance on `Multiplicative (ZMod 2)` produced by
    -- `TopologicalAbelianization.lift` differs syntactically from the quantified one.
    have h₂ : ((TopologicalAbelianization.lift χ').comp
        (e.symm : A →ₜ* TopologicalAbelianization G)) (π g) = χ' g := by
      rw [hπ_apply]
      exact (congrArg (TopologicalAbelianization.lift χ') (e.symm_apply_apply _)).trans
        (TopologicalAbelianization.lift_mk χ' g)
    exact (hφ (π g)).trans (congrArg Multiplicative.toAdd h₂)

/-! ### Demushkin groups at `p = 2` -/

variable [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsDemushkin 2 G)
include hG

namespace IsDemushkin

/-- **Every continuous character `G → 𝔽₂` of a Demushkin group at `p = 2` lifts to `ℤ/4` exactly
when `q(G) ≠ 2`.** Through `G^{ab} ≅ ℤ_2^{n-1} × ℤ_2 ⧸ (q)`: if `q ≠ 2` then `4 ∣ q` and every
character lifts coordinatewise, while if `q = 2` the projection onto the torsion factor
`ℤ_2 ⧸ (2) = 𝔽₂` does not lift. -/
theorem forall_exists_zmodFourReduction_eq_iff_demushkinQ_ne_two :
    (∀ χ : continuousZModDual 2 G, ∃ φ : G →ₜ* Multiplicative (ZMod 4),
      φ.zmodFourReduction = χ) ↔ demushkinQ hG ≠ 2 := by
  obtain ⟨e⟩ := hG.nonempty_continuousMulEquiv_topologicalAbelianization
  rw [forall_exists_zmodFourReduction_eq_iff_of_topologicalAbelianization e]
  refine ⟨fun h hq ↦ ?_, fun hq χ ↦ ?_⟩
  · rw [hq, Nat.cast_ofNat] at h
    obtain ⟨φ, hφ⟩ := h (PadicInt.piProdQuotientSpanToZMod (q := (2 : ℤ_[2])) (dvd_refl _))
    obtain ⟨a, ha⟩ := PadicInt.exists_castHom_toAdd_ne_toAdd_piProdQuotientSpanToZMod φ
    exact ha (hφ a)
  · refine PadicInt.exists_forall_castHom_toAdd_eq_toAdd_of_pow_two_dvd ?_ χ
    rcases eq_or_ne (demushkinQ hG) 0 with h0 | h0
    · rw [h0, Nat.cast_zero]
      exact dvd_zero _
    · obtain ⟨k, hk, hqk⟩ := hG.exists_demushkinQ_eq_pow h0
      have hk2 : 2 ≤ k := by
        by_contra hlt
        exact hq (by rw [hqk, show k = 1 by omega, pow_one])
      rw [hqk, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_dvd_pow _ hk2

/-- **The cup form of a Demushkin group at `p = 2` is alternating exactly when `q(G) ≠ 2`**: every
cup square on `H¹(G, 𝔽₂)` vanishes if and only if `q(G) ≠ 2`. -/
theorem forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two :
    (∀ a : cohomFp 2 G 1, cupFp 2 G a a = 0) ↔ demushkinQ hG ≠ 2 :=
  forall_cupFp_self_eq_zero_iff_forall_exists_zmodFourReduction_eq.trans
    hG.forall_exists_zmodFourReduction_eq_iff_demushkinQ_ne_two

/-- **The cup form of a Demushkin group at `p = 2` is not alternating exactly when `q(G) = 2`**:
some cup square on `H¹(G, 𝔽₂)` is nonzero if and only if `q(G) = 2`. -/
theorem exists_cupFp_self_ne_zero_iff_demushkinQ_eq_two :
    (∃ a : cohomFp 2 G 1, cupFp 2 G a a ≠ 0) ↔ demushkinQ hG = 2 := by
  simpa [not_forall] using hG.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two.not

/-- At `p = 2`, a Demushkin group with `q(G) ≠ 2` has even rank: its cup form is a nondegenerate
alternating form on `H¹(G, 𝔽₂)`. -/
theorem even_demushkinRank_of_demushkinQ_ne_two (hq : demushkinQ hG ≠ 2) :
    Even (demushkinRank hG) :=
  hG.even_demushkinRank_of_forall_cupFp_self_eq_zero
    (hG.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two.2 hq)

/-- At `p = 2`, a Demushkin group of odd rank has `q(G) = 2`. -/
theorem demushkinQ_eq_two_of_odd_demushkinRank (hn : Odd (demushkinRank hG)) :
    demushkinQ hG = 2 :=
  by_contra fun hq ↦ (Nat.not_even_iff_odd.2 hn) (hG.even_demushkinRank_of_demushkinQ_ne_two hq)

end IsDemushkin

end TauCeti
