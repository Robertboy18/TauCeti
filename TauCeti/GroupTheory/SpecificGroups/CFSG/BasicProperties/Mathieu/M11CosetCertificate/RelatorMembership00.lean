/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 00

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r0_mem : r0 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 0 < 64 by decide))

theorem r1_mem : r1 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 1 < 64 by decide))

theorem r2_mem : r2 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 2 < 64 by decide))

theorem r3_mem : r3 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 3 < 64 by decide))

theorem r4_mem : r4 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 4 < 64 by decide))

theorem r5_mem : r5 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 5 < 64 by decide))

theorem r6_mem : r6 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 6 < 64 by decide))

theorem r7_mem : r7 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 7 < 64 by decide))

theorem r8_mem : r8 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 8 < 64 by decide))

theorem r9_mem : r9 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 9 < 64 by decide))

theorem r10_mem : r10 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 10 < 64 by decide))

theorem r11_mem : r11 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 11 < 64 by decide))

theorem r12_mem : r12 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 12 < 64 by decide))

theorem r13_mem : r13 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 13 < 64 by decide))

theorem r14_mem : r14 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 14 < 64 by decide))

theorem r15_mem : r15 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 15 < 64 by decide))

theorem r16_mem : r16 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 16 < 64 by decide))

theorem r17_mem : r17 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 17 < 64 by decide))

theorem r18_mem : r18 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 18 < 64 by decide))

theorem r19_mem : r19 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 19 < 64 by decide))

theorem r20_mem : r20 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 20 < 64 by decide))

theorem r21_mem : r21 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 21 < 64 by decide))

theorem r22_mem : r22 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 22 < 64 by decide))

theorem r23_mem : r23 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 23 < 64 by decide))

theorem r24_mem : r24 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 24 < 64 by decide))

theorem r25_mem : r25 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 25 < 64 by decide))

theorem r26_mem : r26 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 26 < 64 by decide))

theorem r27_mem : r27 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 27 < 64 by decide))

theorem r28_mem : r28 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 28 < 64 by decide))

theorem r29_mem : r29 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 29 < 64 by decide))

theorem r30_mem : r30 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 30 < 64 by decide))

theorem r31_mem : r31 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 31 < 64 by decide))

theorem r32_mem : r32 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 32 < 64 by decide))

theorem r33_mem : r33 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 33 < 64 by decide))

theorem r34_mem : r34 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 34 < 64 by decide))

theorem r35_mem : r35 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 35 < 64 by decide))

theorem r36_mem : r36 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 36 < 64 by decide))

theorem r37_mem : r37 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 37 < 64 by decide))

theorem r38_mem : r38 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 38 < 64 by decide))

theorem r39_mem : r39 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 39 < 64 by decide))

theorem r40_mem : r40 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 40 < 64 by decide))

theorem r41_mem : r41 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 41 < 64 by decide))

theorem r42_mem : r42 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 42 < 64 by decide))

theorem r43_mem : r43 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 43 < 64 by decide))

theorem r44_mem : r44 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 44 < 64 by decide))

theorem r45_mem : r45 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 45 < 64 by decide))

theorem r46_mem : r46 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 46 < 64 by decide))

theorem r47_mem : r47 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 47 < 64 by decide))

theorem r48_mem : r48 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 48 < 64 by decide))

theorem r49_mem : r49 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 49 < 64 by decide))

theorem r50_mem : r50 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 50 < 64 by decide))

theorem r51_mem : r51 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 51 < 64 by decide))

theorem r52_mem : r52 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 52 < 64 by decide))

theorem r53_mem : r53 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 53 < 64 by decide))

theorem r54_mem : r54 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 54 < 64 by decide))

theorem r55_mem : r55 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 55 < 64 by decide))

theorem r56_mem : r56 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 56 < 64 by decide))

theorem r57_mem : r57 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 57 < 64 by decide))

theorem r58_mem : r58 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 58 < 64 by decide))

theorem r59_mem : r59 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 59 < 64 by decide))

theorem r60_mem : r60 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 60 < 64 by decide))

theorem r61_mem : r61 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 61 < 64 by decide))

theorem r62_mem : r62 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 62 < 64 by decide))

theorem r63_mem : r63 ∈ relators := by
  unfold relators
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk00) (show 63 < 64 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
