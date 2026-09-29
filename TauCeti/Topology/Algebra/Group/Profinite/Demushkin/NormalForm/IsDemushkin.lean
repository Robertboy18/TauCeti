/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Abelianization
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Finite
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Criterion

/-!
# The normal-form presentations define Demushkin groups

Let `F = freeProP p (Fin n)` be the free pro-`p` group on `n` generators `x₁, …, x_n`. The three
families of one-relator pro-`p` groups presented by Labute's normal-form words,

* `⟨x₁, …, x_n ∣ x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` for `p ∣ q` and `n ≥ 2` even;
* `⟨x₁, …, x_n ∣ x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)⟩` for `p = 2`, `f ≥ 2` and `n` odd;
* `⟨x₁, …, x_n ∣ x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` for `p = 2`, `4 ∣ a`,
  `f ≥ 2` and `n ≥ 2` even,

are Demushkin groups of rank `n`. This is the realization step of the existence theorem of the
classification of Demushkin groups: each normal-form presentation is an actual Demushkin group of
the expected rank; which closed subgroup of `ℤ_pˣ` its canonical character has as image is a
separate statement about the orientations of the normal forms. The proof is Labute's criterion,
`TauCeti.isDemushkin_of_nondegenerate_degreeOneForm`: a one-relator pro-`p` group
`⟨X ∣ r⟩` with `r ∈ Φ(F)` and `X` nonempty is Demushkin exactly when the degree-one form of the
class of `r` in `gr_1(F)` is nondegenerate, and the degree-one forms of the three normal-form words
are nondegenerate by direct computation
(`TauCeti.freeProP.nondegenerate_degreeOneForm_demushkinWordNeTwo`,
`TauCeti.freeProP.nondegenerate_degreeOneForm_demushkinWordTwoOdd`,
`TauCeti.freeProP.nondegenerate_degreeOneForm_demushkinWordTwoEven`). The rank is `n` because the
normal-form presentations are minimal.

The dyadic group `D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` is the odd-rank normal form with `n = 3` and
`f = 2`; it is therefore an infinite Demushkin group of rank `3`, and its `q`-invariant is `2`,
read off the torsion subgroup of its abelianization `D₀^{ab} ≅ ℤ₂ × ℤ₂ × ℤ/2`.

## Main results

* `TauCeti.isDemushkin_presentedProP_demushkinWordNeTwo`,
  `TauCeti.isDemushkin_presentedProP_demushkinWordTwoOdd`,
  `TauCeti.isDemushkin_presentedProP_demushkinWordTwoEven`: **the normal-form presented groups
  are Demushkin groups**.
* `TauCeti.demushkinRank_presentedProP_demushkinWordNeTwo`,
  `TauCeti.demushkinRank_presentedProP_demushkinWordTwoOdd`,
  `TauCeti.demushkinRank_presentedProP_demushkinWordTwoEven`: the rank of any of these Demushkin
  groups is the number `n` of generators.
* `TauCeti.isDemushkin_demushkinD0`, `TauCeti.demushkinRank_demushkinD0`,
  `TauCeti.demushkinQ_demushkinD0`: **`D₀` is a Demushkin group** of rank `3` with `q(D₀) = 2`,
  and it is infinite.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Proposition 3 and Theorem 3, and p. 106.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
-/

public section

namespace TauCeti

open freeProP
open CommGroup (torsion)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-! ### The normal-form presented groups are Demushkin groups -/

/-- **The alternating normal form defines a Demushkin group.** For `p ∣ q` and `n ≥ 2` even, the
pro-`p` group presented on `n` generators by `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` is a
Demushkin group. This covers `q = 0`, where the relator is `(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem isDemushkin_presentedProP_demushkinWordNeTwo (hn : Even n) (hn0 : n ≠ 0) {q : ℕ}
    (hq : p ∣ q) :
    IsDemushkin p (presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)}) :=
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  isDemushkin_of_nondegenerate_degreeOneForm
    (demushkinWordNeTwo_mem_proPFrattini Fact.out hq n _) (ContinuousMulEquiv.refl _)
    (nondegenerate_degreeOneForm_demushkinWordNeTwo hn hq)

/-- **The alternating normal form on `n` generators has rank `n`**, for `p ∣ q`, whenever it is
a Demushkin group. -/
@[simp]
theorem demushkinRank_presentedProP_demushkinWordNeTwo {q : ℕ} (hq : p ∣ q)
    (hG : IsDemushkin p (presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)})) :
    demushkinRank hG = n := by
  rw [demushkinRank_def]
  exact topologicalGeneratorRankNat_presentedProP_demushkinWordNeTwo hq n

/-- **The dyadic odd-rank normal form defines a Demushkin group.** For `f ≥ 2` and `n` odd, the
pro-`2` group presented on `n` generators by `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` is a
Demushkin group. At `n = 1` the word is `x₁²` and the group is `ℤ/2`. -/
theorem isDemushkin_presentedProP_demushkinWordTwoOdd (hn : Odd n) {f : ℕ} (hf : 2 ≤ f) :
    IsDemushkin 2 (presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)}) :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  isDemushkin_of_nondegenerate_degreeOneForm
    (demushkinWordTwoOdd_mem_proPFrattini (zero_lt_two.trans_le hf) n _)
    (ContinuousMulEquiv.refl _) (nondegenerate_degreeOneForm_demushkinWordTwoOdd hn hf)

/-- **The dyadic odd-rank normal form on `n` generators has rank `n`**, for `f ≥ 1`, whenever it
is a Demushkin group. -/
@[simp]
theorem demushkinRank_presentedProP_demushkinWordTwoOdd {f : ℕ} (hf : 0 < f)
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)})) :
    demushkinRank hG = n := by
  rw [demushkinRank_def]
  exact topologicalGeneratorRankNat_presentedProP_demushkinWordTwoOdd hf n

/-- **The dyadic even-rank normal form defines a Demushkin group.** For `4 ∣ a`, `f ≥ 2` and
`n ≥ 2` even, the pro-`2` group presented on `n` generators by
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` is a Demushkin group. -/
theorem isDemushkin_presentedProP_demushkinWordTwoEven (hn : Even n) (hn0 : n ≠ 0) {a f : ℕ}
    (ha : 4 ∣ a) (hf : 2 ≤ f) :
    IsDemushkin 2 (presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)}) :=
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  isDemushkin_of_nondegenerate_degreeOneForm
    (demushkinWordTwoEven_mem_proPFrattini (dvd_trans (Dvd.intro 2 rfl) ha)
      (zero_lt_two.trans_le hf) n _)
    (ContinuousMulEquiv.refl _) (nondegenerate_degreeOneForm_demushkinWordTwoEven hn ha hf)

/-- **The dyadic even-rank normal form on `n` generators has rank `n`**, for `a` even and
`f ≥ 1`, whenever it is a Demushkin group. -/
@[simp]
theorem demushkinRank_presentedProP_demushkinWordTwoEven {a f : ℕ} (ha : 2 ∣ a) (hf : 0 < f)
    (hG : IsDemushkin 2
      (presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)})) :
    demushkinRank hG = n := by
  rw [demushkinRank_def]
  exact topologicalGeneratorRankNat_presentedProP_demushkinWordTwoEven ha hf n

/-! ### The dyadic group `D₀` -/

/-- **`D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` is a Demushkin group at `p = 2`**: its relator is the dyadic
odd-rank normal-form word with `n = 3` and `f = 2`. -/
theorem isDemushkin_demushkinD0 : IsDemushkin 2 demushkinD0 := by
  have h := isDemushkin_presentedProP_demushkinWordTwoOdd (n := 3) ⟨1, rfl⟩ (f := 2) le_rfl
  rwa [← d0Relator_eq_demushkinWordTwoOdd] at h

/-- **`D₀` is a Demushkin group of rank `3`.** -/
@[simp]
theorem demushkinRank_demushkinD0 (hG : IsDemushkin 2 demushkinD0) : demushkinRank hG = 3 := by
  rw [demushkinRank_def, topologicalGeneratorRankNat_demushkinD0]

/-- **`D₀` is infinite**, being a Demushkin group of rank `3 ≥ 2`. -/
instance : Infinite demushkinD0 :=
  isDemushkin_demushkinD0.infinite_of_two_le_demushkinRank
    (by rw [demushkinRank_demushkinD0]; omega)

/-- **`q(D₀) = 2`**: the `q`-invariant of `D₀`, the number of torsion elements of its
abelianization `D₀^{ab} ≅ ℤ₂ × ℤ₂ × ℤ/2`. -/
@[simp]
theorem demushkinQ_demushkinD0 (hG : IsDemushkin 2 demushkinD0) : demushkinQ hG = 2 := by
  have hcard := nat_card_torsion_topologicalAbelianization_demushkinD0
  rw [demushkinQ_of_not_isMulTorsionFree _ fun h ↦ ?_, hcard]
  rw [CommGroup.isMulTorsionFree_iff_torsion_eq_bot.1 h, Subgroup.card_bot] at hcard
  omega

end TauCeti
