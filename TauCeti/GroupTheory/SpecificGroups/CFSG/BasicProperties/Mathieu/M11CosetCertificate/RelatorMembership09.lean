/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 09

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r576_mem : r576 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 0 < 56 by decide))

theorem r577_mem : r577 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 1 < 56 by decide))

theorem r578_mem : r578 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 2 < 56 by decide))

theorem r579_mem : r579 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 3 < 56 by decide))

theorem r580_mem : r580 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 4 < 56 by decide))

theorem r581_mem : r581 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 5 < 56 by decide))

theorem r582_mem : r582 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 6 < 56 by decide))

theorem r583_mem : r583 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 7 < 56 by decide))

theorem r584_mem : r584 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 8 < 56 by decide))

theorem r585_mem : r585 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 9 < 56 by decide))

theorem r586_mem : r586 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 10 < 56 by decide))

theorem r587_mem : r587 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 11 < 56 by decide))

theorem r588_mem : r588 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 12 < 56 by decide))

theorem r589_mem : r589 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 13 < 56 by decide))

theorem r590_mem : r590 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 14 < 56 by decide))

theorem r591_mem : r591 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 15 < 56 by decide))

theorem r592_mem : r592 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 16 < 56 by decide))

theorem r593_mem : r593 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 17 < 56 by decide))

theorem r594_mem : r594 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 18 < 56 by decide))

theorem r595_mem : r595 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 19 < 56 by decide))

theorem r596_mem : r596 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 20 < 56 by decide))

theorem r597_mem : r597 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 21 < 56 by decide))

theorem r598_mem : r598 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 22 < 56 by decide))

theorem r599_mem : r599 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 23 < 56 by decide))

theorem r600_mem : r600 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 24 < 56 by decide))

theorem r601_mem : r601 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 25 < 56 by decide))

theorem r602_mem : r602 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 26 < 56 by decide))

theorem r603_mem : r603 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 27 < 56 by decide))

theorem r604_mem : r604 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 28 < 56 by decide))

theorem r605_mem : r605 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 29 < 56 by decide))

theorem r606_mem : r606 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 30 < 56 by decide))

theorem r607_mem : r607 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 31 < 56 by decide))

theorem r608_mem : r608 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 32 < 56 by decide))

theorem r609_mem : r609 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 33 < 56 by decide))

theorem r610_mem : r610 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 34 < 56 by decide))

theorem r611_mem : r611 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 35 < 56 by decide))

theorem r612_mem : r612 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 36 < 56 by decide))

theorem r613_mem : r613 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 37 < 56 by decide))

theorem r614_mem : r614 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 38 < 56 by decide))

theorem r615_mem : r615 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 39 < 56 by decide))

theorem r616_mem : r616 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 40 < 56 by decide))

theorem r617_mem : r617 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 41 < 56 by decide))

theorem r618_mem : r618 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 42 < 56 by decide))

theorem r619_mem : r619 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 43 < 56 by decide))

theorem r620_mem : r620 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 44 < 56 by decide))

theorem r621_mem : r621 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 45 < 56 by decide))

theorem r622_mem : r622 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 46 < 56 by decide))

theorem r623_mem : r623 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 47 < 56 by decide))

theorem r624_mem : r624 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 48 < 56 by decide))

theorem r625_mem : r625 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 49 < 56 by decide))

theorem r626_mem : r626 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 50 < 56 by decide))

theorem r627_mem : r627 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 51 < 56 by decide))

theorem r628_mem : r628 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 52 < 56 by decide))

theorem r629_mem : r629 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 53 < 56 by decide))

theorem r630_mem : r630 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 54 < 56 by decide))

theorem r631_mem : r631 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk09) (show 55 < 56 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
