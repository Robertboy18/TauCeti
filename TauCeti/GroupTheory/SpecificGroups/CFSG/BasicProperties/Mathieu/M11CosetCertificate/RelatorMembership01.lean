/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 01

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r64_mem : r64 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 0 < 64 by decide))

theorem r65_mem : r65 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 1 < 64 by decide))

theorem r66_mem : r66 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 2 < 64 by decide))

theorem r67_mem : r67 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 3 < 64 by decide))

theorem r68_mem : r68 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 4 < 64 by decide))

theorem r69_mem : r69 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 5 < 64 by decide))

theorem r70_mem : r70 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 6 < 64 by decide))

theorem r71_mem : r71 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 7 < 64 by decide))

theorem r72_mem : r72 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 8 < 64 by decide))

theorem r73_mem : r73 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 9 < 64 by decide))

theorem r74_mem : r74 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 10 < 64 by decide))

theorem r75_mem : r75 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 11 < 64 by decide))

theorem r76_mem : r76 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 12 < 64 by decide))

theorem r77_mem : r77 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 13 < 64 by decide))

theorem r78_mem : r78 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 14 < 64 by decide))

theorem r79_mem : r79 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 15 < 64 by decide))

theorem r80_mem : r80 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 16 < 64 by decide))

theorem r81_mem : r81 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 17 < 64 by decide))

theorem r82_mem : r82 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 18 < 64 by decide))

theorem r83_mem : r83 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 19 < 64 by decide))

theorem r84_mem : r84 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 20 < 64 by decide))

theorem r85_mem : r85 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 21 < 64 by decide))

theorem r86_mem : r86 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 22 < 64 by decide))

theorem r87_mem : r87 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 23 < 64 by decide))

theorem r88_mem : r88 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 24 < 64 by decide))

theorem r89_mem : r89 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 25 < 64 by decide))

theorem r90_mem : r90 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 26 < 64 by decide))

theorem r91_mem : r91 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 27 < 64 by decide))

theorem r92_mem : r92 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 28 < 64 by decide))

theorem r93_mem : r93 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 29 < 64 by decide))

theorem r94_mem : r94 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 30 < 64 by decide))

theorem r95_mem : r95 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 31 < 64 by decide))

theorem r96_mem : r96 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 32 < 64 by decide))

theorem r97_mem : r97 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 33 < 64 by decide))

theorem r98_mem : r98 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 34 < 64 by decide))

theorem r99_mem : r99 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 35 < 64 by decide))

theorem r100_mem : r100 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 36 < 64 by decide))

theorem r101_mem : r101 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 37 < 64 by decide))

theorem r102_mem : r102 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 38 < 64 by decide))

theorem r103_mem : r103 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 39 < 64 by decide))

theorem r104_mem : r104 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 40 < 64 by decide))

theorem r105_mem : r105 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 41 < 64 by decide))

theorem r106_mem : r106 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 42 < 64 by decide))

theorem r107_mem : r107 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 43 < 64 by decide))

theorem r108_mem : r108 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 44 < 64 by decide))

theorem r109_mem : r109 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 45 < 64 by decide))

theorem r110_mem : r110 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 46 < 64 by decide))

theorem r111_mem : r111 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 47 < 64 by decide))

theorem r112_mem : r112 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 48 < 64 by decide))

theorem r113_mem : r113 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 49 < 64 by decide))

theorem r114_mem : r114 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 50 < 64 by decide))

theorem r115_mem : r115 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 51 < 64 by decide))

theorem r116_mem : r116 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 52 < 64 by decide))

theorem r117_mem : r117 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 53 < 64 by decide))

theorem r118_mem : r118 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 54 < 64 by decide))

theorem r119_mem : r119 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 55 < 64 by decide))

theorem r120_mem : r120 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 56 < 64 by decide))

theorem r121_mem : r121 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 57 < 64 by decide))

theorem r122_mem : r122 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 58 < 64 by decide))

theorem r123_mem : r123 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 59 < 64 by decide))

theorem r124_mem : r124 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 60 < 64 by decide))

theorem r125_mem : r125 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 61 < 64 by decide))

theorem r126_mem : r126 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 62 < 64 by decide))

theorem r127_mem : r127 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk01) (show 63 < 64 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
