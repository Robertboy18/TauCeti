/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded

/-!
# Power and bracket in degree zero of the lower `p`-series

The binomial collection formula gives the correction to compatibility of the power operator
with the bracket when the powered input has degree zero. For odd `p` the correction vanishes;
for `p = 2` it is an iterated bracket.

The power/bracket compatibility laws follow the `GradedPowerLaws` blueprint in the Tau Ceti
roadmap's `ProfiniteProPGroups/Suggested.lean`. The degree-zero extensions follow the
Layer 8 discussion in the roadmap README.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1,
  Propositions 1 and 2.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u

variable {G : Type u} [Group G]

private theorem commutatorElement_pow_left_of_central {a b : G}
    (h : ∀ g : G, Commute g ⁅a, ⁅a, b⁆⁆) (n : ℕ) :
    ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n * ⁅a, ⁅a, b⁆⁆ ^ n.choose 2 := by
  let c := ⁅a, b⁆
  let t := b * a * b⁻¹
  let d := ⁅a, c⁆
  have hc : Commute c d := h c
  have ht : Commute t d := h t
  have htc : ⁅t, c⁆ = d := by
    calc
      ⁅t, c⁆ = c⁻¹ * d * c := by
        dsimp [c, t, d]
        simp only [commutatorElement_def]
        group
      _ = d := by rw [hc.inv_left.eq]; group
  have hct : c * t = a := by
    dsimp [c, t]
    rw [commutatorElement_def]
    group
  have hpow := Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
    (a := c) (b := t) (by rwa [htc]) (by rwa [htc]) n
  rw [hct, htc] at hpow
  have ht_pow : t ^ n = b * a ^ n * b⁻¹ :=
    (map_pow (MulAut.conj b) a n).symm
  calc
    ⁅a ^ n, b⁆ = a ^ n * (t ^ n)⁻¹ := by rw [ht_pow, commutatorElement_def]; group
    _ = c ^ n * t ^ n * d ^ n.choose 2 * (t ^ n)⁻¹ := by rw [hpow]
    _ = c ^ n * d ^ n.choose 2 := by
      rw [mul_assoc (c ^ n) (t ^ n), ((ht.pow_left n).pow_right (n.choose 2)).eq]
      group

private theorem commutatorElement_pow_right_of_central {a b : G}
    (h : ∀ g : G, Commute g ⁅b, ⁅a, b⁆⁆) (n : ℕ) :
    ⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n * ⁅b, ⁅a, b⁆⁆ ^ n.choose 2 := by
  have hswap : ⁅b, ⁅b, a⁆⁆ = ⁅b, ⁅a, b⁆⁆⁻¹ := by
    rw [← commutatorElement_inv a b]
    calc
      ⁅b, ⁅a, b⁆⁻¹⁆ = ⁅a, b⁆⁻¹ * ⁅b, ⁅a, b⁆⁆⁻¹ * ⁅a, b⁆ := by
        generalize ⁅a, b⁆ = c
        simp only [commutatorElement_def]
        group
      _ = ⁅b, ⁅a, b⁆⁆⁻¹ := by
        rw [(h ⁅a, b⁆).inv_left.inv_right.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hleft := commutatorElement_pow_left_of_central (a := b) (b := a)
    (fun g => by rw [hswap]; exact (h g).inv_right) n
  calc
    ⁅a, b ^ n⁆ = (⁅b, ⁅b, a⁆⁆ ^ n.choose 2)⁻¹ * (⁅b, a⁆ ^ n)⁻¹ := by
      simpa only [commutatorElement_inv, mul_inv_rev] using congrArg Inv.inv hleft
    _ = ⁅b, ⁅a, b⁆⁆ ^ n.choose 2 * ⁅a, b⁆ ^ n := by
      rw [hswap, ← inv_pow, inv_inv, ← inv_pow, commutatorElement_inv]
    _ = ⁅a, b⁆ ^ n * ⁅b, ⁅a, b⁆⁆ ^ n.choose 2 :=
      ((h ⁅a, b⁆).pow_left n |>.pow_right (n.choose 2)).eq.symm

variable {p : ℕ} [TopologicalSpace G] [IsTopologicalGroup G]

/-- Collection of a powered commutator modulo `λ_{k+3}`. The iterated commutator lies in
`λ_{k+2}`, so its image is central and the binomial formula applies. -/
theorem mk_commutatorElement_pow_left {k : ℕ} {a b : G}
    (hb : b ∈ pLowerCentralSeries p G k) (n : ℕ) :
    ((⁅a ^ n, b⁆ : G) : G ⧸ pLowerCentralSeries p G (k + 2 + 1)) =
      ((⁅a, b⁆ ^ n * ⁅a, ⁅a, b⁆⁆ ^ n.choose 2 : G) : G ⧸ _) := by
  have ha : a ∈ pLowerCentralSeries p G 0 := by simp
  have hd : ⁅a, ⁅a, b⁆⁆ ∈ pLowerCentralSeries p G (k + 2) := by
    simpa only [zero_add, Nat.add_assoc] using
      commutator_mem_pLowerCentralSeries ha (commutator_mem_pLowerCentralSeries ha hb)
  simp only [← QuotientGroup.mk'_apply, map_commutatorElement, map_pow, map_mul]
  apply commutatorElement_pow_left_of_central
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
    commute_mk_of_mem_pLowerCentralSeries hd g

/-- Collection in the right input modulo `λ_{j+3}`. The correction involves
`⁅b, ⁅a, b⁆⁆`; reversing the outer commutator would change its sign. -/
theorem mk_commutatorElement_pow_right {j : ℕ} {a b : G}
    (ha : a ∈ pLowerCentralSeries p G j) (n : ℕ) :
    ((⁅a, b ^ n⁆ : G) : G ⧸ pLowerCentralSeries p G (j + 2 + 1)) =
      ((⁅a, b⁆ ^ n * ⁅b, ⁅a, b⁆⁆ ^ n.choose 2 : G) : G ⧸ _) := by
  have hb : b ∈ pLowerCentralSeries p G 0 := by simp
  have hd : ⁅b, ⁅a, b⁆⁆ ∈ pLowerCentralSeries p G (j + 2) := by
    simpa only [zero_add, add_zero, Nat.add_assoc] using
      commutator_mem_pLowerCentralSeries hb (commutator_mem_pLowerCentralSeries ha hb)
  simp only [← QuotientGroup.mk'_apply, map_commutatorElement, map_pow, map_mul]
  apply commutatorElement_pow_right_of_central
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
    commute_mk_of_mem_pLowerCentralSeries hd g

/-- The correction to `[π x, y] = π [x, y]` when `x` has degree zero is
`(p choose 2) • [x, [x, y]]`, transported to the degree of `π [x, y]`. -/
theorem gradedBracket_gradedPow_zero_left {k : ℕ} (x : gradedPiece p G 0)
    (y : gradedPiece p G k) :
    gradedCast p G (show 1 + k + 1 = 0 + k + 1 + 1 by omega)
        (gradedBracket p G 1 k (gradedPow p G 0 x) y) =
      gradedPow p G (0 + k + 1) (gradedBracket p G 0 k x y) +
        p.choose 2 • gradedCast p G (by omega)
          (gradedBracket p G 0 (0 + k + 1) x (gradedBracket p G 0 k x y)) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective 0 x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  simp only [gradedPow_gradedMk, gradedBracket_gradedMk, gradedCast_gradedMk,
    ← gradedMk_pow, ← gradedMk_mul, gradedMk_eq_gradedMk_iff, coe_mul, coe_pow]
  have hdegree : k + 2 + 1 = 0 + k + 1 + 1 + 1 := by omega
  exact hdegree ▸ mk_commutatorElement_pow_left (a := (x : G)) y.2 p

/-- The correction to `[x, π y] = π [x, y]` when `y` has degree zero is
`(p choose 2) • [y, [x, y]]`, with the inner bracket in this order. -/
theorem gradedBracket_gradedPow_zero_right {j : ℕ} (x : gradedPiece p G j)
    (y : gradedPiece p G 0) :
    gradedCast p G (show j + 1 + 1 = j + 0 + 1 + 1 by omega)
        (gradedBracket p G j 1 x (gradedPow p G 0 y)) =
      gradedPow p G (j + 0 + 1) (gradedBracket p G j 0 x y) +
        p.choose 2 • gradedCast p G (by omega)
          (gradedBracket p G 0 (j + 0 + 1) y (gradedBracket p G j 0 x y)) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective 0 y
  simp only [gradedPow_gradedMk, gradedBracket_gradedMk, gradedCast_gradedMk,
    ← gradedMk_pow, ← gradedMk_mul, gradedMk_eq_gradedMk_iff, coe_mul, coe_pow]
  simpa only [add_zero, Nat.add_assoc] using
    mk_commutatorElement_pow_right (b := (y : G)) x.2 p

/-- For odd `p`, the power operator commutes with the bracket on the left in every degree,
including degree zero. No primality assumption is needed. -/
theorem gradedPow_gradedBracket_left_of_odd (hp : Odd p) {j k : ℕ}
    (x : gradedPiece p G j) (y : gradedPiece p G k) :
    gradedPow p G (j + k + 1) (gradedBracket p G j k x y) =
      gradedCast p G (by omega) (gradedBracket p G (j + 1) k (gradedPow p G j x) y) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h := gradedBracket_gradedPow_zero_left x y
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (Nat.Odd.sub_odd hp odd_one).two_dvd,
      mul_nsmul, nsmul_gradedPiece_eq_zero, nsmul_zero] at h
    simpa only [add_zero] using h.symm
  · exact gradedPow_gradedBracket_left hj x y

/-- For odd `p`, the power operator commutes with the bracket on the right in every degree,
including degree zero. No primality assumption is needed. -/
theorem gradedPow_gradedBracket_right_of_odd (hp : Odd p) {j k : ℕ}
    (x : gradedPiece p G j) (y : gradedPiece p G k) :
    gradedPow p G (j + k + 1) (gradedBracket p G j k x y) =
      gradedCast p G (by omega) (gradedBracket p G j (k + 1) x (gradedPow p G k y)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h := gradedBracket_gradedPow_zero_right x y
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (Nat.Odd.sub_odd hp odd_one).two_dvd,
      mul_nsmul, nsmul_gradedPiece_eq_zero, nsmul_zero] at h
    simpa only [add_zero] using h.symm
  · exact gradedPow_gradedBracket_right hk x y

private theorem neg_gradedPiece_two {k : ℕ} (x : gradedPiece 2 G k) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]
  exact (two_nsmul _).symm.trans (nsmul_gradedPiece_eq_zero _)

private theorem gradedCast_trans {i j k : ℕ} (hij : i = j) (hjk : j = k)
    (x : gradedPiece p G i) :
    gradedCast p G hjk (gradedCast p G hij x) = gradedCast p G (hij.trans hjk) x := by
  subst hij
  subst hjk
  simp only [gradedCast_rfl]

/-- For `p = 2` and `x` of degree zero, `[π x, y] = π [x, y] + [[x, y], x]`.
The last term has this orientation because every graded piece is killed by `2`. -/
theorem gradedBracket_gradedPow_zero_left_of_two (hp : p = 2) {k : ℕ}
    (x : gradedPiece p G 0) (y : gradedPiece p G k) :
    gradedCast p G (show 1 + k + 1 = 0 + k + 1 + 1 by omega)
        (gradedBracket p G 1 k (gradedPow p G 0 x) y) =
      gradedPow p G (0 + k + 1) (gradedBracket p G 0 k x y) +
        gradedCast p G (by omega)
          (gradedBracket p G (0 + k + 1) 0 (gradedBracket p G 0 k x y) x) := by
  subst hp
  rw [gradedBracket_gradedPow_zero_left, Nat.choose_self, one_nsmul]
  congr 1
  have h := congrArg (gradedCast 2 G (show 0 + (0 + k + 1) + 1 = 0 + k + 1 + 1 by omega))
    (gradedCast_gradedBracket_swap x (gradedBracket 2 G 0 k x y))
  simpa only [gradedCast_trans, gradedCast_rfl, gradedCast_neg, neg_gradedPiece_two] using h.symm

/-- For `p = 2` and `y` of degree zero, `[x, π y] = π [x, y] + [[x, y], y]`.
The inner bracket retains the order `[x, y]`. -/
theorem gradedBracket_gradedPow_zero_right_of_two (hp : p = 2) {j : ℕ}
    (x : gradedPiece p G j) (y : gradedPiece p G 0) :
    gradedCast p G (show j + 1 + 1 = j + 0 + 1 + 1 by omega)
        (gradedBracket p G j 1 x (gradedPow p G 0 y)) =
      gradedPow p G (j + 0 + 1) (gradedBracket p G j 0 x y) +
        gradedCast p G (by omega)
          (gradedBracket p G (j + 0 + 1) 0 (gradedBracket p G j 0 x y) y) := by
  subst hp
  rw [gradedBracket_gradedPow_zero_right, Nat.choose_self, one_nsmul]
  congr 1
  have h := congrArg (gradedCast 2 G (show 0 + (j + 0 + 1) + 1 = j + 0 + 1 + 1 by omega))
    (gradedCast_gradedBracket_swap y (gradedBracket 2 G j 0 x y))
  simpa only [gradedCast_trans, gradedCast_rfl, gradedCast_neg, neg_gradedPiece_two] using h.symm

end TauCeti
