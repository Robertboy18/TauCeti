/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.LowRank
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Binary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Realization
import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass
import TauCeti.NumberTheory.LocalField.Squares

/-!
# Isotropy of quadratic forms over a local field, rank by rank

Let `K` be a nonarchimedean local field in which `2` is invertible. Whether a regular quadratic
form over `K` is isotropic is decided by its rank `n`, its plain discriminant `d ∈ Kˣ/(Kˣ)²` and
its local Hasse invariant `s = ∏_{i<j} (aᵢ, aⱼ)_K`:

* `n = 1`: never isotropic, and `n = 2`: isotropic exactly when `d = [-1]`; these two hold over
  every field (`TauCeti.RegularFormClass.anisotropic_of_rank_le_one`,
  `TauCeti.RegularFormClass.not_anisotropic_iff_discr_eq_neg_one_of_rank_eq_two`);
* `n = 3`: isotropic exactly when `s = (-1, -d)_K`;
* `n = 4`: isotropic exactly when `d ≠ [1]`, or `d = [1]` and `s = (-1, -1)_K`;
* `n ≥ 5`: always isotropic.

In particular the `u`-invariant of `K` is four: every regular form of rank at least five is
isotropic, and there is an anisotropic form of rank four, namely any form with invariants
`(4, [1], -(-1, -1)_K)`.

The ternary and quaternary criteria reduce to the binary one, which says that a regular binary
form `⟨a, b⟩` represents a unit `c` exactly when `(c, -ab)_K = (a, b)_K`. A ternary form
`⟨a, b, c⟩` is isotropic exactly when `⟨a, b⟩` represents `-c`. A quaternary form
`⟨a, b⟩ ⊥ ⟨c, d⟩` is isotropic exactly when `⟨a, b⟩` and `⟨-c, -d⟩` have a common nonzero value,
which is a question about the two characters `(·, -ab)_K` and `(·, -cd)_K` of `Kˣ`: they are
distinct when `abcd` is a nonsquare, and two distinct nontrivial characters of a group of exponent
two take every pair of values. A form of rank five contains a binary form, whose values fill two
square classes, and a ternary form, which represents every unit outside one square class.

## Main results

* `TauCeti.exists_hilbertSymbol_eq_and_hilbertSymbol_eq`: for nonsquares `a`, `b` with `ab` a
  nonsquare, the characters `(·, a)_K` and `(·, b)_K` take every pair of values.
* `TauCeti.exists_not_isSquare_hilbertSymbol_eq_one`: the norm group of `K(√a)` contains a
  nonsquare, for every `a`.
* `TauCeti.RegularFormClass.not_anisotropic_iff_localHasse_eq_of_rank_eq_three`: the ternary
  criterion `s = (-1, -d)_K`.
* `TauCeti.RegularFormClass.not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four`:
  the quaternary criterion `d ≠ [1] ∨ s = (-1, -1)_K`.
* `TauCeti.RegularFormClass.not_anisotropic_of_five_le_rank`: every class of rank at least five
  is isotropic.
* `TauCeti.RegularFormClass.exists_rank_eq_four_and_anisotropic`: there is an anisotropic class of
  rank four, so `u(K) = 4`.
* `QuadraticForm.not_anisotropic_iff_localHasse_eq_of_finrank_eq_three`,
  `QuadraticForm.not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_finrank_eq_four`,
  `QuadraticForm.not_anisotropic_of_five_le_finrank`: the same criteria for regular forms on
  finite-dimensional spaces.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.2, Theorem 6.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:17–63:19.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter VI, §2.
-/

public section

open Finset QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-! ### Prescribing two values of the Hilbert symbol -/

/-- **The norm group of `K(√a)` contains a nonsquare.** For every `a ∈ Kˣ` there is a nonsquare
`b` with `(b, a)_K = 1`: among a uniformizer `π`, the unramified unit `Δ` and their product, three
nonsquares, the symbols with `a` multiply to `1`, so one of them is `1`. -/
theorem exists_not_isSquare_hilbertSymbol_eq_one (a : Kˣ) :
    ∃ b : Kˣ, ¬IsSquare b ∧ hilbertSymbol b a = 1 := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  obtain ⟨Δ, hΔ, hΔv, -⟩ := exists_unramified_class h2
  by_cases hπa : hilbertSymbol π a = 1
  · exact ⟨π, not_isSquare_of_isUniformizer hπ, hπa⟩
  by_cases hΔa : hilbertSymbol Δ a = 1
  · exact ⟨Δ, hΔ, hΔa⟩
  refine ⟨π * Δ,
    not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation hπ (hΔv ▸ Even.zero), ?_⟩
  rw [hilbertSymbol_mul_left h2, Int.units_ne_iff_eq_neg.mp hπa, Int.units_ne_iff_eq_neg.mp hΔa]
  decide

/-- For a nonsquare `a` and any `b` with `ab` a nonsquare, some `y ∈ Kˣ` has `(y, a)_K = -1` and
`(y, b)_K = 1`: the character `(·, a)_K` is nontrivial and differs from `(·, b)_K`. -/
theorem exists_hilbertSymbol_eq_neg_one_and_eq_one {a b : Kˣ} (ha : ¬IsSquare a)
    (hab : ¬IsSquare (a * b)) :
    ∃ y : Kˣ, hilbertSymbol y a = -1 ∧ hilbertSymbol y b = 1 := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  obtain ⟨x₁, hx₁⟩ := exists_hilbertSymbol_eq_neg_one h2 ha
  obtain ⟨x₃, hx₃⟩ := exists_hilbertSymbol_eq_neg_one h2 hab
  rw [hilbertSymbol_comm] at hx₁ hx₃
  rw [hilbertSymbol_mul_right h2] at hx₃
  rcases Int.units_eq_one_or (hilbertSymbol x₁ b) with h₁ | h₁
  · exact ⟨x₁, hx₁, h₁⟩
  rcases Int.units_eq_one_or (hilbertSymbol x₃ a) with h₃ | h₃
  · rw [h₃, one_mul] at hx₃
    exact ⟨x₁ * x₃, by rw [hilbertSymbol_mul_left h2, hx₁, h₃, mul_one],
      by rw [hilbertSymbol_mul_left h2, h₁, hx₃]; decide⟩
  · rw [h₃, neg_one_mul, neg_inj] at hx₃
    exact ⟨x₃, h₃, hx₃⟩

/-- **Two distinct nontrivial characters take every pair of values.** For nonsquares `a`, `b`
with `ab` a nonsquare, every pair of signs `(s, t)` is `((x, a)_K, (x, b)_K)` for some
`x ∈ Kˣ`. -/
theorem exists_hilbertSymbol_eq_and_hilbertSymbol_eq {a b : Kˣ} (ha : ¬IsSquare a)
    (hb : ¬IsSquare b) (hab : ¬IsSquare (a * b)) (s t : ℤˣ) :
    ∃ x : Kˣ, hilbertSymbol x a = s ∧ hilbertSymbol x b = t := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  obtain ⟨y, hya, hyb⟩ := exists_hilbertSymbol_eq_neg_one_and_eq_one ha hab
  obtain ⟨z, hzb, hza⟩ := exists_hilbertSymbol_eq_neg_one_and_eq_one hb (mul_comm a b ▸ hab)
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · exact ⟨1, hilbertSymbol_one_left a, hilbertSymbol_one_left b⟩
  · exact ⟨z, hza, hzb⟩
  · exact ⟨y, hya, hyb⟩
  · exact ⟨y * z, by rw [hilbertSymbol_mul_left h2, hya, hza, mul_one],
      by rw [hilbertSymbol_mul_left h2, hyb, hzb, one_mul]⟩

/-! ### Diagonal forms of rank three, four and five -/

/-- **Ternary isotropy** (Serre IV Thm 6 (iii)). A diagonal form `⟨a, b, c⟩` over `K` is
isotropic exactly when its local Hasse invariant `(a, b)(a, c)(b, c)` is `(-1, -abc)_K`. -/
theorem not_anisotropic_presentedForm_three_iff (w : Fin 3 → Kˣ) :
    ¬(presentedForm ⟨3, w⟩).Anisotropic ↔
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 1) (w 2) =
        hilbertSymbol (-1) (-(w 0 * w 1 * w 2)) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  -- `⟨w₀, w₁, w₂⟩` is isotropic exactly when `⟨w₁, w₂⟩` represents `-w₀`, that is, when
  -- `(-w₀, -w₁w₂)_K = (w₁, w₂)_K`.
  have htail : presentedForm ⟨2, fun i : Fin 2 => w i.succ⟩ =
      weightedSumSquares K ![(w 1 : K), (w 2 : K)] := by
    rw [presentedForm_eq_weightedSumSquares_coe]
    congr 1
    funext i
    fin_cases i <;> rfl
  refine (not_anisotropic_presentedForm_succ_iff w).trans ?_
  rw [htail, mem_unitValueSet_binary_iff_hilbertSymbol_eq]
  -- Both products expand to the same seven symbols.
  have key : hilbertSymbol (-w 0) (-(w 1 * w 2)) * hilbertSymbol (w 1) (w 2) =
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 1) (w 2) *
        hilbertSymbol (-1) (-(w 0 * w 1 * w 2)) := by
    rw [neg_eq_neg_one_mul (w 0), neg_eq_neg_one_mul (w 1 * w 2),
      neg_eq_neg_one_mul (w 0 * w 1 * w 2)]
    simp only [hilbertSymbol_mul_left h2, hilbertSymbol_mul_right h2]
    rw [hilbertSymbol_comm (w 0) (-1)]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  -- Two signs agree exactly when their product is `1`.
  constructor
  · intro h
    refine (mul_eq_one_iff_eq_inv.mp ?_).trans (Int.units_inv_eq_self _)
    rw [← key, h, Int.units_mul_self]
  · intro h
    refine (mul_eq_one_iff_eq_inv.mp ?_).trans (Int.units_inv_eq_self _)
    rw [key, h, Int.units_mul_self]

/-- If `abcd` is a nonsquare, the binary forms `⟨a, b⟩` and `⟨c, d⟩` have unit values `x` and
`-x` that are negatives of each other, so that `⟨a, b⟩ ⊥ ⟨c, d⟩` is isotropic. -/
theorem exists_mem_unitValueSet_binary_and_neg_mem_of_not_isSquare (a b c d : Kˣ)
    (h : ¬IsSquare (a * b * c * d)) :
    ∃ x : Kˣ, x ∈ unitValueSet (weightedSumSquares K ![(a : K), (b : K)]) ∧
      -x ∈ unitValueSet (weightedSumSquares K ![(c : K), (d : K)]) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have hab : hilbertSymbol a (-(a * b)) = hilbertSymbol a b :=
    (mem_unitValueSet_binary_iff_hilbertSymbol_eq a b a).mp (mem_unitValueSet_binary_left a b)
  have hcd : hilbertSymbol c (-(c * d)) = hilbertSymbol c d :=
    (mem_unitValueSet_binary_iff_hilbertSymbol_eq c d c).mp (mem_unitValueSet_binary_left c d)
  simp only [mem_unitValueSet_binary_iff_hilbertSymbol_eq]
  by_cases hab' : IsSquare (-(a * b))
  · -- `⟨a, b⟩` is a hyperbolic plane and represents every unit, in particular `-c`.
    refine ⟨-c, ?_, ?_⟩
    · rw [hilbertSymbol_eq_one_of_isSquare_right _ hab', ← hab,
        hilbertSymbol_eq_one_of_isSquare_right _ hab']
    · rw [neg_neg, hcd]
  by_cases hcd' : IsSquare (-(c * d))
  · -- `⟨c, d⟩` is a hyperbolic plane and represents every unit, in particular `-a`.
    refine ⟨a, hab, ?_⟩
    rw [hilbertSymbol_eq_one_of_isSquare_right _ hcd', ← hcd,
      hilbertSymbol_eq_one_of_isSquare_right _ hcd']
  -- Otherwise `(·, -ab)_K` and `(·, -cd)_K` are distinct nontrivial characters.
  have hprod : ¬IsSquare (-(a * b) * -(c * d)) := by rwa [neg_mul_neg, ← mul_assoc]
  obtain ⟨x, hx₁, hx₂⟩ := exists_hilbertSymbol_eq_and_hilbertSymbol_eq hab' hcd' hprod
    (hilbertSymbol a b) (hilbertSymbol (-1) (-(c * d)) * hilbertSymbol c d)
  refine ⟨x, hx₁, ?_⟩
  rw [neg_eq_neg_one_mul x, hilbertSymbol_mul_left h2, hx₂, ← mul_assoc, Int.units_mul_self,
    one_mul]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Invertible (2 : K)] in
/-- The first two weights of a quaternary presentation, as a binary diagonal form. -/
private theorem presentedForm_castAdd_two (w : Fin 4 → Kˣ) :
    presentedForm ⟨2, fun i => w (Fin.castAdd 2 i)⟩ =
      weightedSumSquares K ![(w 0 : K), (w 1 : K)] := by
  rw [presentedForm_eq_weightedSumSquares_coe]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Invertible (2 : K)] in
/-- The last two weights of a quaternary presentation, as a binary diagonal form. -/
private theorem presentedForm_natAdd_two (w : Fin 4 → Kˣ) :
    presentedForm ⟨2, fun i => w (Fin.natAdd 2 i)⟩ =
      weightedSumSquares K ![(w 2 : K), (w 3 : K)] := by
  rw [presentedForm_eq_weightedSumSquares_coe]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **Quaternary isotropy, nonsquare discriminant** (Serre IV Thm 6 (iv)). A diagonal form
`⟨a, b, c, d⟩` over `K` whose discriminant `abcd` is a nonsquare is isotropic. -/
theorem not_anisotropic_presentedForm_four_of_not_isSquare (w : Fin 4 → Kˣ)
    (h : ¬IsSquare (w 0 * w 1 * w 2 * w 3)) : ¬(presentedForm ⟨4, w⟩).Anisotropic := by
  intro hani
  have hprod :=
    (equivalent_presentedForm_prod_castAdd_natAdd (m := 2) (n := 2) w).anisotropic_iff.mp hani
  rw [presentedForm_castAdd_two, presentedForm_natAdd_two] at hprod
  obtain ⟨x, hx₁, hx₂⟩ :=
    exists_mem_unitValueSet_binary_and_neg_mem_of_not_isSquare (w 0) (w 1) (w 2) (w 3) h
  exact not_anisotropic_prod_of_represents_neg (mem_unitValueSet.mp hx₁)
    (by simpa using mem_unitValueSet.mp hx₂) x.ne_zero hprod

/-- **Quaternary isotropy, square discriminant** (Serre IV Thm 6 (iv)). A diagonal form
`⟨a, b, c, d⟩` over `K` whose discriminant `abcd` is a square is isotropic exactly when its local
Hasse invariant `∏_{i<j} (aᵢ, aⱼ)_K` is `(-1, -1)_K`. -/
theorem not_anisotropic_presentedForm_four_iff_of_isSquare (w : Fin 4 → Kˣ)
    (h : IsSquare (w 0 * w 1 * w 2 * w 3)) :
    ¬(presentedForm ⟨4, w⟩).Anisotropic ↔
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 0) (w 3) *
        hilbertSymbol (w 1) (w 2) * hilbertSymbol (w 1) (w 3) * hilbertSymbol (w 2) (w 3) =
          hilbertSymbol (-1 : Kˣ) (-1) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have hab : hilbertSymbol (w 0) (-(w 0 * w 1)) = hilbertSymbol (w 0) (w 1) :=
    (mem_unitValueSet_binary_iff_hilbertSymbol_eq (w 0) (w 1) (w 0)).mp
      (mem_unitValueSet_binary_left (w 0) (w 1))
  -- `⟨w₀, w₁⟩ ⊥ ⟨w₂, w₃⟩` is isotropic exactly when `⟨w₀, w₁⟩` has a unit value `x` with `-x` a
  -- value of `⟨w₂, w₃⟩`.
  have hiff : ¬(presentedForm ⟨4, w⟩).Anisotropic ↔
      ∃ x : Kˣ, x ∈ unitValueSet (weightedSumSquares K ![(w 0 : K), (w 1 : K)]) ∧
        -x ∈ unitValueSet (weightedSumSquares K ![(w 2 : K), (w 3 : K)]) := by
    rw [← presentedForm_castAdd_two w, ← presentedForm_natAdd_two w]
    refine ((equivalent_presentedForm_prod_castAdd_natAdd (m := 2) (n := 2)
      w).anisotropic_iff.not).trans ?_
    constructor
    · intro hiso
      by_cases hcd : (presentedForm ⟨2, fun i => w (Fin.natAdd 2 i)⟩).Anisotropic
      · obtain ⟨x, y, hx, hxy⟩ := hcd.exists_ne_zero_eq_neg_of_not_anisotropic_prod
          (nondegenerate_presentedForm _).radical_eq_bot hiso
        refine ⟨Units.mk0 _ hx, mem_unitValueSet.mpr ((represents_iff _ _).mpr ⟨x, rfl⟩),
          mem_unitValueSet.mpr ((represents_iff _ _).mpr ⟨y, ?_⟩)⟩
        rw [Units.val_neg, Units.val_mk0, hxy, neg_neg]
      · -- An isotropic `⟨w₂, w₃⟩` represents every scalar, in particular `-w₀`.
        refine ⟨w 0, ?_, ?_⟩
        · rw [presentedForm_castAdd_two]
          exact mem_unitValueSet_binary_left (w 0) (w 1)
        · rw [mem_unitValueSet, Units.val_neg]
          exact represents_of_nondegenerate_of_not_anisotropic _ (nondegenerate_presentedForm _)
            hcd _
    · rintro ⟨x, hx₁, hx₂⟩
      exact not_anisotropic_prod_of_represents_neg (mem_unitValueSet.mp hx₁)
        (by simpa using mem_unitValueSet.mp hx₂) x.ne_zero
  -- Since `-w₀w₁` and `-w₂w₃` lie in the same square class, the two characters `(·, -w₀w₁)_K`
  -- and `(·, -w₂w₃)_K` agree, and `w₀` itself is a value of `⟨w₀, w₁⟩`; so the condition is
  -- `(-1, -w₀w₁)_K (w₀, w₁)_K = (w₂, w₃)_K`.
  have hcong (x : Kˣ) : hilbertSymbol x (-(w 2 * w 3)) = hilbertSymbol x (-(w 0 * w 1)) :=
    hilbertSymbol_congr_sq x x _ _ ⟨x, rfl⟩ (by rwa [neg_mul_neg, mul_comm, ← mul_assoc])
  have hneg (x : Kˣ) : hilbertSymbol (-x) (-(w 0 * w 1)) =
      hilbertSymbol (-1) (-(w 0 * w 1)) * hilbertSymbol x (-(w 0 * w 1)) := by
    rw [neg_eq_neg_one_mul x, hilbertSymbol_mul_left h2]
  rw [hiff]
  simp only [mem_unitValueSet_binary_iff_hilbertSymbol_eq, hcong]
  -- The two products expand to the same symbols, once `(w₀w₁, w₂w₃)_K = (-1, w₀w₁)_K` is used.
  have key : hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 2) (w 3) *
      hilbertSymbol (-1) (-(w 0 * w 1)) =
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 0) (w 3) *
        hilbertSymbol (w 1) (w 2) * hilbertSymbol (w 1) (w 3) * hilbertSymbol (w 2) (w 3) *
          hilbertSymbol (-1 : Kˣ) (-1) := by
    have habcd : hilbertSymbol (w 0 * w 1) (w 2 * w 3) = hilbertSymbol (-1 : Kˣ) (w 0 * w 1) := by
      rw [hilbertSymbol_congr_sq (w 0 * w 1) (w 0 * w 1) (w 2 * w 3) (w 0 * w 1) ⟨w 0 * w 1, rfl⟩
        (by rwa [mul_comm, ← mul_assoc]), hilbertSymbol_self, hilbertSymbol_comm]
    rw [neg_eq_neg_one_mul (w 0 * w 1), hilbertSymbol_mul_right h2, ← habcd]
    simp only [hilbertSymbol_mul_left h2, hilbertSymbol_mul_right h2]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  constructor
  · rintro ⟨x, hx₁, hx₂⟩
    rw [hneg x, hx₁] at hx₂
    refine (mul_eq_one_iff_eq_inv.mp ?_).trans (Int.units_inv_eq_self _)
    rw [← key, ← hx₂]
    have hcomm : hilbertSymbol (w 0) (w 1) *
        (hilbertSymbol (-1) (-(w 0 * w 1)) * hilbertSymbol (w 0) (w 1)) *
          hilbertSymbol (-1) (-(w 0 * w 1)) =
        hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 1) *
          (hilbertSymbol (-1) (-(w 0 * w 1)) * hilbertSymbol (-1) (-(w 0 * w 1))) := by
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [hcomm, Int.units_mul_self, Int.units_mul_self, one_mul]
  · intro hε
    refine ⟨w 0, hab, ?_⟩
    rw [hneg (w 0), hab]
    refine (mul_eq_one_iff_eq_inv.mp ?_).trans (Int.units_inv_eq_self _)
    rw [mul_comm _ (hilbertSymbol (w 0) (w 1)), mul_right_comm, key, hε, Int.units_mul_self]

/-- **Isotropy in rank five** (Serre IV Thm 6 (v)). Every diagonal form of rank five over `K`
is isotropic. -/
theorem not_anisotropic_presentedForm_five (w : Fin 5 → Kˣ) :
    ¬(presentedForm ⟨5, w⟩).Anisotropic := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  intro hani
  have hprod :=
    (equivalent_presentedForm_prod_castAdd_natAdd (m := 2) (n := 3) w).anisotropic_iff.mp hani
  have hfirst : presentedForm ⟨2, fun i => w (Fin.castAdd 3 i)⟩ =
      weightedSumSquares K ![(w 0 : K), (w 1 : K)] := by
    rw [presentedForm_eq_weightedSumSquares_coe]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hlast : (fun i : Fin 3 => w (Fin.natAdd 2 i)) = ![w 2, w 3, w 4] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hfirst, hlast] at hprod
  -- A unit value `x` of `⟨w₀, w₁⟩` with `-x` a value of `⟨w₂, w₃, w₄⟩` contradicts anisotropy.
  have hval (x : Kˣ) (hx : x ∈ unitValueSet (weightedSumSquares K ![(w 0 : K), (w 1 : K)]))
      (hx' : -x ∈ unitValueSet (presentedForm ⟨3, ![w 2, w 3, w 4]⟩)) : False :=
    not_anisotropic_prod_of_represents_neg (mem_unitValueSet.mp hx)
      (by simpa using mem_unitValueSet.mp hx') x.ne_zero hprod
  -- `⟨w₂, w₃, w₄⟩` represents `-x` as soon as `⟨x, w₂, w₃, w₄⟩` has a nonsquare discriminant.
  have hter (x : Kˣ) (hx : ¬IsSquare (x * (w 2 * w 3 * w 4))) :
      -x ∈ unitValueSet (presentedForm ⟨3, ![w 2, w 3, w 4]⟩) := by
    have h4 := (not_anisotropic_presentedForm_succ_iff ![x, w 2, w 3, w 4]).mp
      (not_anisotropic_presentedForm_four_of_not_isSquare ![x, w 2, w 3, w 4]
        (by simpa [mul_assoc] using hx))
    -- The tail of `⟨x, w₂, w₃, w₄⟩` is `⟨w₂, w₃, w₄⟩`; the rewrite goes through the dependent
    -- rank index, which `simp` cannot do.
    have htail : (fun i : Fin 3 => ![x, w 2, w 3, w 4] i.succ) = ![w 2, w 3, w 4] :=
      funext fun i => by fin_cases i <;> rfl
    rw [htail] at h4
    simpa using h4
  -- The values `w₀` and `w₀ n` of `⟨w₀, w₁⟩`, with `n` a nonsquare norm from `K(√(-w₀w₁))`, lie
  -- in distinct square classes, so one of them has a nonsquare product with `w₂w₃w₄`.
  obtain ⟨n, hn, hn'⟩ := exists_not_isSquare_hilbertSymbol_eq_one (-(w 0 * w 1))
  have hw0 : w 0 ∈ unitValueSet (weightedSumSquares K ![(w 0 : K), (w 1 : K)]) :=
    mem_unitValueSet_binary_left _ _
  have hw0n : w 0 * n ∈ unitValueSet (weightedSumSquares K ![(w 0 : K), (w 1 : K)]) := by
    rw [mem_unitValueSet_binary_iff_hilbertSymbol_eq, hilbertSymbol_mul_left h2, hn', mul_one]
    exact (mem_unitValueSet_binary_iff_hilbertSymbol_eq _ _ _).mp hw0
  by_cases hsq : IsSquare (w 0 * (w 2 * w 3 * w 4))
  · refine hval _ hw0n (hter _ fun h => hn ?_)
    have hcancel : w 0 * n * (w 2 * w 3 * w 4) * (w 0 * (w 2 * w 3 * w 4))⁻¹ = n := by
      rw [mul_right_comm (w 0) n, mul_comm (w 0 * (w 2 * w 3 * w 4)) n, mul_inv_cancel_right]
    exact hcancel ▸ h.mul hsq.inv
  · exact hval _ hw0 (hter _ hsq)

/-- **Isotropy in rank at least five.** Every diagonal form of rank at least five over `K` is
isotropic. -/
theorem not_anisotropic_presentedForm_of_five_le {n : ℕ} (hn : 5 ≤ n) (w : Fin n → Kˣ) :
    ¬(presentedForm ⟨n, w⟩).Anisotropic := by
  induction n, hn using Nat.le_induction with
  | base => exact not_anisotropic_presentedForm_five w
  | succ n _ ih => exact (presentedForm_tail_isRepresentedBy w).not_anisotropic (ih _)

/-! ### The isotropy list on isometry classes -/

namespace RegularFormClass

/-- **Ternary isotropy** (Serre IV Thm 6 (iii)). A regular-form class of rank three over `K` is
isotropic exactly when its local Hasse invariant is `(-1, -d)_K`, where `d` is its
discriminant. -/
theorem not_anisotropic_iff_localHasse_eq_of_rank_eq_three {x : RegularFormClass K}
    (hx : x.rank = 3) :
    ¬x.Anisotropic ↔ localHasse x =
      hilbertSymbolOnSquareClasses (squareClass (-1 : Kˣ)) (squareClass (-1 : Kˣ) + discr x) := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    subst hx
    rw [anisotropic_mk, not_anisotropic_presentedForm_three_iff, localHasse_mk,
      prod_prod_Ioi_three, discr_mk, Fin.prod_univ_three, ← squareClass_mul,
      hilbertSymbolOnSquareClasses_squareClass, neg_one_mul]

/-- **Quaternary isotropy** (Serre IV Thm 6 (iv)). A regular-form class of rank four over `K` is
isotropic exactly when its discriminant is not the class of `1`, or its discriminant is the class
of `1` and its local Hasse invariant is `(-1, -1)_K`. -/
theorem not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four
    {x : RegularFormClass K} (hx : x.rank = 4) :
    ¬x.Anisotropic ↔ discr x ≠ 0 ∨ localHasse x = hilbertSymbol (-1 : Kˣ) (-1) := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    subst hx
    rw [anisotropic_mk, discr_mk, Fin.prod_univ_four, ne_eq, squareClass_eq_zero_iff,
      localHasse_mk, prod_prod_Ioi_four]
    dsimp only
    by_cases h : IsSquare (w 0 * w 1 * w 2 * w 3)
    · rw [not_anisotropic_presentedForm_four_iff_of_isSquare w h]
      simp only [h, not_true_eq_false, false_or]
    · simp only [h, not_false_eq_true, true_or, iff_true]
      exact not_anisotropic_presentedForm_four_of_not_isSquare w h

/-- **Isotropy in rank at least five** (Serre IV Thm 6 (v)). Every regular-form class of rank at
least five over `K` is isotropic. -/
theorem not_anisotropic_of_five_le_rank {x : RegularFormClass K} (hx : 5 ≤ x.rank) :
    ¬x.Anisotropic := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [rank_mk] at hx
    rw [anisotropic_mk]
    exact not_anisotropic_presentedForm_of_five_le hx p.2

/-- **`u(K) = 4`** (O'Meara 63:19). There is an anisotropic regular-form class of rank four over
`K`: any class with trivial discriminant and local Hasse invariant `-(-1, -1)_K`. -/
theorem exists_rank_eq_four_and_anisotropic :
    ∃ x : RegularFormClass K, x.rank = 4 ∧ x.Anisotropic := by
  obtain ⟨x, hx, hd, hs⟩ := exists_of_realization (K := K) (n := 4) (by norm_num) 0
    (-hilbertSymbol (-1 : Kˣ) (-1)) (fun h => by omega) (fun h => by omega)
  refine ⟨x, hx, not_not.mp fun h => ?_⟩
  rcases (not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four hx).mp h with
    hd' | hs'
  · exact hd' hd
  · exact Int.units_ne_iff_eq_neg.mpr rfl (hs.symm.trans hs')

end RegularFormClass

end TauCeti

/-! ### The isotropy list on quadratic forms -/

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Ternary isotropy** (Serre IV Thm 6 (iii)). A regular quadratic form on a space of dimension
three over `K` is isotropic exactly when its local Hasse invariant is `(-1, -d)_K`, where `d` is
its discriminant. -/
theorem not_anisotropic_iff_localHasse_eq_of_finrank_eq_three (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ¬Q.Anisotropic ↔ RegularFormClass.localHasse (formClass Q hQ) =
      hilbertSymbolOnSquareClasses (squareClass (-1 : Kˣ))
        (squareClass (-1 : Kˣ) + RegularFormClass.discr (formClass Q hQ)) := by
  rw [← anisotropic_formClass Q hQ]
  exact RegularFormClass.not_anisotropic_iff_localHasse_eq_of_rank_eq_three
    (by rwa [rank_formClass])

/-- **Quaternary isotropy** (Serre IV Thm 6 (iv)). A regular quadratic form on a space of
dimension four over `K` is isotropic exactly when its discriminant is not the class of `1`, or its
discriminant is the class of `1` and its local Hasse invariant is `(-1, -1)_K`. -/
theorem not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_finrank_eq_four
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4) :
    ¬Q.Anisotropic ↔ RegularFormClass.discr (formClass Q hQ) ≠ 0 ∨
      RegularFormClass.localHasse (formClass Q hQ) = hilbertSymbol (-1 : Kˣ) (-1) := by
  rw [← anisotropic_formClass Q hQ]
  exact RegularFormClass.not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four
    (by rwa [rank_formClass])

/-- **Isotropy in dimension at least five** (Serre IV Thm 6 (v)). Every regular quadratic form on
a space of dimension at least five over `K` is isotropic. -/
theorem not_anisotropic_of_five_le_finrank (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV : 5 ≤ Module.finrank K V) : ¬Q.Anisotropic := by
  rw [← anisotropic_formClass Q hQ]
  exact RegularFormClass.not_anisotropic_of_five_le_rank (by rwa [rank_formClass])

end QuadraticForm
