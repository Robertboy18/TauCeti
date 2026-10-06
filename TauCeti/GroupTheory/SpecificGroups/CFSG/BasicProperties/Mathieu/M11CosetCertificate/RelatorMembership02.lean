/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 02

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r128_mem : r128 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 0 < 64 by decide))

theorem r129_mem : r129 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 1 < 64 by decide))

theorem r130_mem : r130 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 2 < 64 by decide))

theorem r131_mem : r131 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 3 < 64 by decide))

theorem r132_mem : r132 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 4 < 64 by decide))

theorem r133_mem : r133 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 5 < 64 by decide))

theorem r134_mem : r134 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 6 < 64 by decide))

theorem r135_mem : r135 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 7 < 64 by decide))

theorem r136_mem : r136 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 8 < 64 by decide))

theorem r137_mem : r137 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 9 < 64 by decide))

theorem r138_mem : r138 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 10 < 64 by decide))

theorem r139_mem : r139 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 11 < 64 by decide))

theorem r140_mem : r140 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 12 < 64 by decide))

theorem r141_mem : r141 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 13 < 64 by decide))

theorem r142_mem : r142 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 14 < 64 by decide))

theorem r143_mem : r143 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 15 < 64 by decide))

theorem r144_mem : r144 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 16 < 64 by decide))

theorem r145_mem : r145 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 17 < 64 by decide))

theorem r146_mem : r146 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 18 < 64 by decide))

theorem r147_mem : r147 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 19 < 64 by decide))

theorem r148_mem : r148 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 20 < 64 by decide))

theorem r149_mem : r149 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 21 < 64 by decide))

theorem r150_mem : r150 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 22 < 64 by decide))

theorem r151_mem : r151 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 23 < 64 by decide))

theorem r152_mem : r152 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 24 < 64 by decide))

theorem r153_mem : r153 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 25 < 64 by decide))

theorem r154_mem : r154 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 26 < 64 by decide))

theorem r155_mem : r155 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 27 < 64 by decide))

theorem r156_mem : r156 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 28 < 64 by decide))

theorem r157_mem : r157 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 29 < 64 by decide))

theorem r158_mem : r158 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 30 < 64 by decide))

theorem r159_mem : r159 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 31 < 64 by decide))

theorem r160_mem : r160 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 32 < 64 by decide))

theorem r161_mem : r161 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 33 < 64 by decide))

theorem r162_mem : r162 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 34 < 64 by decide))

theorem r163_mem : r163 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 35 < 64 by decide))

theorem r164_mem : r164 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 36 < 64 by decide))

theorem r165_mem : r165 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 37 < 64 by decide))

theorem r166_mem : r166 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 38 < 64 by decide))

theorem r167_mem : r167 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 39 < 64 by decide))

theorem r168_mem : r168 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 40 < 64 by decide))

theorem r169_mem : r169 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 41 < 64 by decide))

theorem r170_mem : r170 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 42 < 64 by decide))

theorem r171_mem : r171 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 43 < 64 by decide))

theorem r172_mem : r172 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 44 < 64 by decide))

theorem r173_mem : r173 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 45 < 64 by decide))

theorem r174_mem : r174 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 46 < 64 by decide))

theorem r175_mem : r175 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 47 < 64 by decide))

theorem r176_mem : r176 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 48 < 64 by decide))

theorem r177_mem : r177 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 49 < 64 by decide))

theorem r178_mem : r178 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 50 < 64 by decide))

theorem r179_mem : r179 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 51 < 64 by decide))

theorem r180_mem : r180 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 52 < 64 by decide))

theorem r181_mem : r181 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 53 < 64 by decide))

theorem r182_mem : r182 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 54 < 64 by decide))

theorem r183_mem : r183 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 55 < 64 by decide))

theorem r184_mem : r184 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 56 < 64 by decide))

theorem r185_mem : r185 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 57 < 64 by decide))

theorem r186_mem : r186 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 58 < 64 by decide))

theorem r187_mem : r187 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 59 < 64 by decide))

theorem r188_mem : r188 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 60 < 64 by decide))

theorem r189_mem : r189 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 61 < 64 by decide))

theorem r190_mem : r190 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 62 < 64 by decide))

theorem r191_mem : r191 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk02) (show 63 < 64 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
