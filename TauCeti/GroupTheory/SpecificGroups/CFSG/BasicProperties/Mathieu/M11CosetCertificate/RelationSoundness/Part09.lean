/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelationSoundness.Basic

/-! Exact relations for the concrete words in the M11 coset certificate. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness

open Relations

/-- Trimmed scan word 576 holds in the exact presentation group. -/
theorem r576_eq_one : (r576.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word478 true
    10 word478_eq_one (by decide +kernel)

/-- Trimmed scan word 577 holds in the exact presentation group. -/
theorem r577_eq_one : (r577.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word500 false
    6 word500_eq_one (by decide +kernel)

/-- Trimmed scan word 578 holds in the exact presentation group. -/
theorem r578_eq_one : (r578.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word500 false
    11 word500_eq_one (by decide +kernel)

/-- Trimmed scan word 579 holds in the exact presentation group. -/
theorem r579_eq_one : (r579.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word500 true
    2 word500_eq_one (by decide +kernel)

/-- Trimmed scan word 580 holds in the exact presentation group. -/
theorem r580_eq_one : (r580.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word500 true
    7 word500_eq_one (by decide +kernel)

/-- Trimmed scan word 581 holds in the exact presentation group. -/
theorem r581_eq_one : (r581.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word512 false
    7 word512_eq_one (by decide +kernel)

/-- Trimmed scan word 582 holds in the exact presentation group. -/
theorem r582_eq_one : (r582.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word512 false
    11 word512_eq_one (by decide +kernel)

/-- Trimmed scan word 583 holds in the exact presentation group. -/
theorem r583_eq_one : (r583.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word512 true
    4 word512_eq_one (by decide +kernel)

/-- Trimmed scan word 584 holds in the exact presentation group. -/
theorem r584_eq_one : (r584.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word512 true
    8 word512_eq_one (by decide +kernel)

/-- Trimmed scan word 585 holds in the exact presentation group. -/
theorem r585_eq_one : (r585.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word523 false
    1 word523_eq_one (by decide +kernel)

/-- Trimmed scan word 586 holds in the exact presentation group. -/
theorem r586_eq_one : (r586.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word523 true
    12 word523_eq_one (by decide +kernel)

/-- Trimmed scan word 587 holds in the exact presentation group. -/
theorem r587_eq_one : (r587.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word617 false
    8 word617_eq_one (by decide +kernel)

/-- Trimmed scan word 588 holds in the exact presentation group. -/
theorem r588_eq_one : (r588.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word617 true
    7 word617_eq_one (by decide +kernel)

/-- Trimmed scan word 589 holds in the exact presentation group. -/
theorem r589_eq_one : (r589.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word619 false
    5 word619_eq_one (by decide +kernel)

/-- Trimmed scan word 590 holds in the exact presentation group. -/
theorem r590_eq_one : (r590.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word619 false
    9 word619_eq_one (by decide +kernel)

/-- Trimmed scan word 591 holds in the exact presentation group. -/
theorem r591_eq_one : (r591.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word619 true
    5 word619_eq_one (by decide +kernel)

/-- Trimmed scan word 592 holds in the exact presentation group. -/
theorem r592_eq_one : (r592.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word619 true
    9 word619_eq_one (by decide +kernel)

/-- Trimmed scan word 593 holds in the exact presentation group. -/
theorem r593_eq_one : (r593.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word642 false
    1 word642_eq_one (by decide +kernel)

/-- Trimmed scan word 594 holds in the exact presentation group. -/
theorem r594_eq_one : (r594.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word642 true
    13 word642_eq_one (by decide +kernel)

/-- Trimmed scan word 595 holds in the exact presentation group. -/
theorem r595_eq_one : (r595.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word646 false
    13 word646_eq_one (by decide +kernel)

/-- Trimmed scan word 596 holds in the exact presentation group. -/
theorem r596_eq_one : (r596.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word646 false
    14 word646_eq_one (by decide +kernel)

/-- Trimmed scan word 597 holds in the exact presentation group. -/
theorem r597_eq_one : (r597.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word646 true
    1 word646_eq_one (by decide +kernel)

/-- Trimmed scan word 598 holds in the exact presentation group. -/
theorem r598_eq_one : (r598.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word646 true
    2 word646_eq_one (by decide +kernel)

/-- Trimmed scan word 599 holds in the exact presentation group. -/
theorem r599_eq_one : (r599.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word687 false
    9 word687_eq_one (by decide +kernel)

/-- Trimmed scan word 600 holds in the exact presentation group. -/
theorem r600_eq_one : (r600.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word687 true
    5 word687_eq_one (by decide +kernel)

/-- Trimmed scan word 601 holds in the exact presentation group. -/
theorem r601_eq_one : (r601.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word691 false
    4 word691_eq_one (by decide +kernel)

/-- Trimmed scan word 602 holds in the exact presentation group. -/
theorem r602_eq_one : (r602.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word691 true
    10 word691_eq_one (by decide +kernel)

/-- Trimmed scan word 603 holds in the exact presentation group. -/
theorem r603_eq_one : (r603.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word736 false
    10 word736_eq_one (by decide +kernel)

/-- Trimmed scan word 604 holds in the exact presentation group. -/
theorem r604_eq_one : (r604.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word736 true
    5 word736_eq_one (by decide +kernel)

/-- Trimmed scan word 605 holds in the exact presentation group. -/
theorem r605_eq_one : (r605.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word845 false
    1 word845_eq_one (by decide +kernel)

/-- Trimmed scan word 606 holds in the exact presentation group. -/
theorem r606_eq_one : (r606.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word845 false
    15 word845_eq_one (by decide +kernel)

/-- Trimmed scan word 607 holds in the exact presentation group. -/
theorem r607_eq_one : (r607.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word845 true
    0 word845_eq_one (by decide +kernel)

/-- Trimmed scan word 608 holds in the exact presentation group. -/
theorem r608_eq_one : (r608.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word845 true
    14 word845_eq_one (by decide +kernel)

/-- Trimmed scan word 609 holds in the exact presentation group. -/
theorem r609_eq_one : (r609.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word856 false
    7 word856_eq_one (by decide +kernel)

/-- Trimmed scan word 610 holds in the exact presentation group. -/
theorem r610_eq_one : (r610.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word856 true
    7 word856_eq_one (by decide +kernel)

/-- Trimmed scan word 611 holds in the exact presentation group. -/
theorem r611_eq_one : (r611.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1014 false
    3 word1014_eq_one (by decide +kernel)

/-- Trimmed scan word 612 holds in the exact presentation group. -/
theorem r612_eq_one : (r612.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1014 false
    5 word1014_eq_one (by decide +kernel)

/-- Trimmed scan word 613 holds in the exact presentation group. -/
theorem r613_eq_one : (r613.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1014 false
    10 word1014_eq_one (by decide +kernel)

/-- Trimmed scan word 614 holds in the exact presentation group. -/
theorem r614_eq_one : (r614.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1014 true
    4 word1014_eq_one (by decide +kernel)

/-- Trimmed scan word 615 holds in the exact presentation group. -/
theorem r615_eq_one : (r615.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1014 true
    9 word1014_eq_one (by decide +kernel)

/-- Trimmed scan word 616 holds in the exact presentation group. -/
theorem r616_eq_one : (r616.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1014 true
    11 word1014_eq_one (by decide +kernel)

/-- Trimmed scan word 617 holds in the exact presentation group. -/
theorem r617_eq_one : (r617.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1015 false
    5 word1015_eq_one (by decide +kernel)

/-- Trimmed scan word 618 holds in the exact presentation group. -/
theorem r618_eq_one : (r618.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1015 true
    7 word1015_eq_one (by decide +kernel)

/-- Trimmed scan word 619 holds in the exact presentation group. -/
theorem r619_eq_one : (r619.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1085 false
    14 word1085_eq_one (by decide +kernel)

/-- Trimmed scan word 620 holds in the exact presentation group. -/
theorem r620_eq_one : (r620.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1085 true
    1 word1085_eq_one (by decide +kernel)

/-- Trimmed scan word 621 holds in the exact presentation group. -/
theorem r621_eq_one : (r621.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1145 false
    15 word1145_eq_one (by decide +kernel)

/-- Trimmed scan word 622 holds in the exact presentation group. -/
theorem r622_eq_one : (r622.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1145 true
    0 word1145_eq_one (by decide +kernel)

/-- Trimmed scan word 623 holds in the exact presentation group. -/
theorem r623_eq_one : (r623.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1163 false
    14 word1163_eq_one (by decide +kernel)

/-- Trimmed scan word 624 holds in the exact presentation group. -/
theorem r624_eq_one : (r624.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1163 true
    1 word1163_eq_one (by decide +kernel)

/-- Trimmed scan word 625 holds in the exact presentation group. -/
theorem r625_eq_one : (r625.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1165 false
    5 word1165_eq_one (by decide +kernel)

/-- Trimmed scan word 626 holds in the exact presentation group. -/
theorem r626_eq_one : (r626.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1165 false
    15 word1165_eq_one (by decide +kernel)

/-- Trimmed scan word 627 holds in the exact presentation group. -/
theorem r627_eq_one : (r627.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1165 true
    10 word1165_eq_one (by decide +kernel)

/-- Trimmed scan word 628 holds in the exact presentation group. -/
theorem r628_eq_one : (r628.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1167 false
    4 word1167_eq_one (by decide +kernel)

/-- Trimmed scan word 629 holds in the exact presentation group. -/
theorem r629_eq_one : (r629.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1167 false
    10 word1167_eq_one (by decide +kernel)

/-- Trimmed scan word 630 holds in the exact presentation group. -/
theorem r630_eq_one : (r630.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1167 true
    4 word1167_eq_one (by decide +kernel)

/-- Trimmed scan word 631 holds in the exact presentation group. -/
theorem r631_eq_one : (r631.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1167 true
    10 word1167_eq_one (by decide +kernel)

@[expose]
def scanBlock36 : List (List (Fin 4)) :=
  [r576, r577, r578, r579, r580,
    r581, r582, r583, r584, r585,
    r586, r587, r588, r589, r590,
    r591]

theorem scanBlock36_eq_one : ∀ w ∈ scanBlock36, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock36, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r576_eq_one
  · exact r577_eq_one
  · exact r578_eq_one
  · exact r579_eq_one
  · exact r580_eq_one
  · exact r581_eq_one
  · exact r582_eq_one
  · exact r583_eq_one
  · exact r584_eq_one
  · exact r585_eq_one
  · exact r586_eq_one
  · exact r587_eq_one
  · exact r588_eq_one
  · exact r589_eq_one
  · exact r590_eq_one
  · exact r591_eq_one

@[expose]
def scanBlock37 : List (List (Fin 4)) :=
  [r592, r593, r594, r595, r596,
    r597, r598, r599, r600, r601,
    r602, r603, r604, r605, r606,
    r607]

theorem scanBlock37_eq_one : ∀ w ∈ scanBlock37, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock37, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r592_eq_one
  · exact r593_eq_one
  · exact r594_eq_one
  · exact r595_eq_one
  · exact r596_eq_one
  · exact r597_eq_one
  · exact r598_eq_one
  · exact r599_eq_one
  · exact r600_eq_one
  · exact r601_eq_one
  · exact r602_eq_one
  · exact r603_eq_one
  · exact r604_eq_one
  · exact r605_eq_one
  · exact r606_eq_one
  · exact r607_eq_one

@[expose]
def scanBlock38 : List (List (Fin 4)) :=
  [r608, r609, r610, r611, r612,
    r613, r614, r615, r616, r617,
    r618, r619, r620, r621, r622,
    r623]

theorem scanBlock38_eq_one : ∀ w ∈ scanBlock38, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock38, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r608_eq_one
  · exact r609_eq_one
  · exact r610_eq_one
  · exact r611_eq_one
  · exact r612_eq_one
  · exact r613_eq_one
  · exact r614_eq_one
  · exact r615_eq_one
  · exact r616_eq_one
  · exact r617_eq_one
  · exact r618_eq_one
  · exact r619_eq_one
  · exact r620_eq_one
  · exact r621_eq_one
  · exact r622_eq_one
  · exact r623_eq_one

@[expose]
def scanBlock39 : List (List (Fin 4)) :=
  [r624, r625, r626, r627, r628,
    r629, r630, r631]

theorem scanBlock39_eq_one : ∀ w ∈ scanBlock39, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock39, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r624_eq_one
  · exact r625_eq_one
  · exact r626_eq_one
  · exact r627_eq_one
  · exact r628_eq_one
  · exact r629_eq_one
  · exact r630_eq_one
  · exact r631_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
