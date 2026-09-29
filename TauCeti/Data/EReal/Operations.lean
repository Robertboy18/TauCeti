/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations

/-!
# Operations on extended real numbers

This file supplements Mathlib's API for arithmetic operations on `EReal`. The common theme is
subtraction in which one operand is a *real* number: both `a - (r : EReal)` and `(r : EReal) - a`
are defined for every extended real `a`, are never of the form `∞ - ∞`, and behave like real
subtraction in the ways recorded here. The first two results below have a real subtrahend and
the last two a real minuend.

## Main results

* `EReal.iInf_sub_coe` and `EReal.iSup_sub_coe` — subtracting a real constant commutes with an
  infimum and with a supremum in `EReal`;
* `EReal.coe_sub_add_coe` — subtracting a sum whose final term is real can be reassociated when
  the minuend is real;
* `EReal.coe_sub_le_comm` — the two subtrahends of a real minuend can be exchanged across an
  inequality, as in `sub_le_comm` for groups;
* `EReal.coe_add_iInf` — adding a real constant commutes with an infimum;
* `EReal.neg_sub_coe` and `EReal.neg_coe_sub` — negating a difference with one real operand
  exchanges the operands, with no finiteness hypothesis on the other;
* `EReal.neg_iSup` and `EReal.neg_iInf` — negation exchanges suprema and infima.
-/

public section

noncomputable section

namespace TauCeti

/-- Subtracting a real constant commutes with an infimum in `EReal`; both sides are `⊤` when the
index type is empty. -/
theorem _root_.EReal.iInf_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨅ i, (f i - (a : EReal))) = (⨅ i, f i) - (a : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i => EReal.sub_le_sub (iInf_le f i) le_rfl)
  rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact le_iInf fun i => EReal.add_le_of_le_sub (iInf_le _ i)

/-- Subtracting a real constant commutes with a supremum in `EReal`; both sides are `⊥` when the
index type is empty. -/
theorem _root_.EReal.iSup_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨆ i, (f i - (a : EReal))) = (⨆ i, f i) - (a : EReal) := by
  refine le_antisymm (iSup_le fun i => EReal.sub_le_sub (le_iSup f i) le_rfl) ?_
  rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact iSup_le fun i =>
    (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))).1
      (le_iSup (fun i => f i - (a : EReal)) i)

/-- Subtracting a sum whose final term is real can be reassociated when the minuend is real. -/
theorem _root_.EReal.coe_sub_add_coe (b : EReal) (d a : ℝ) :
    (d : EReal) - (b + (a : EReal)) = (d : EReal) - b - (a : EReal) := by
  induction b with
  | bot => simp
  | coe b => norm_cast; ring
  | top => simp

/-- With a real minuend, the subtrahend and the right-hand side of an inequality can be
exchanged: `r - a ≤ b ↔ r - b ≤ a`. This is `sub_le_comm` for `EReal`, and it holds with no
finiteness hypothesis on `a` or `b`. -/
theorem _root_.EReal.coe_sub_le_comm {r : ℝ} {a b : EReal} :
    (r : EReal) - a ≤ b ↔ (r : EReal) - b ≤ a := by
  induction a <;> induction b <;> simp [← EReal.coe_sub, add_comm]

/-- Adding a real constant commutes with an infimum in `EReal`; both sides are `⊤` when the
index type is empty. -/
theorem _root_.EReal.coe_add_iInf {ι : Sort*} (a : ℝ) (f : ι → EReal) :
    (a : EReal) + ⨅ i, f i = ⨅ i, ((a : EReal) + f i) := by
  have h := EReal.iInf_sub_coe f (-a)
  simp only [EReal.coe_neg, sub_eq_add_neg, neg_neg, add_comm _ (a : EReal)] at h
  exact h.symm

/-- Negating a difference with a real subtrahend exchanges the operands, for every extended-real
minuend. -/
theorem _root_.EReal.neg_sub_coe (b : EReal) (r : ℝ) : -(b - (r : EReal)) = (r : EReal) - b := by
  induction b with
  | bot => simp
  | coe b => norm_cast; ring
  | top => simp

/-- Negating a difference with a real minuend exchanges the operands, for every extended-real
subtrahend. -/
theorem _root_.EReal.neg_coe_sub (r : ℝ) (b : EReal) : -((r : EReal) - b) = b - (r : EReal) := by
  rw [← EReal.neg_sub_coe, neg_neg]

/-- Negation turns a supremum in `EReal` into the infimum of the negated values. -/
theorem _root_.EReal.neg_iSup {ι : Sort*} (f : ι → EReal) : -(⨆ i, f i) = ⨅ i, -f i := by
  refine le_antisymm (le_iInf fun i => EReal.neg_le_neg_iff.2 (le_iSup f i)) ?_
  rw [EReal.le_neg]
  exact iSup_le fun i => EReal.le_neg.1 (iInf_le (fun i => -f i) i)

/-- Negation turns an infimum in `EReal` into the supremum of the negated values. -/
theorem _root_.EReal.neg_iInf {ι : Sort*} (f : ι → EReal) : -(⨅ i, f i) = ⨆ i, -f i := by
  rw [← neg_neg (⨆ i, -f i), EReal.neg_iSup]
  simp only [neg_neg]

end TauCeti

end

end
