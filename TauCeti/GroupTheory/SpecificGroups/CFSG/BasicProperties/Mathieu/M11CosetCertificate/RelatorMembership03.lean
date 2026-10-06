/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 03

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r192_mem : r192 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 0 < 64 by decide))

theorem r193_mem : r193 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 1 < 64 by decide))

theorem r194_mem : r194 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 2 < 64 by decide))

theorem r195_mem : r195 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 3 < 64 by decide))

theorem r196_mem : r196 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 4 < 64 by decide))

theorem r197_mem : r197 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 5 < 64 by decide))

theorem r198_mem : r198 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 6 < 64 by decide))

theorem r199_mem : r199 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 7 < 64 by decide))

theorem r200_mem : r200 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 8 < 64 by decide))

theorem r201_mem : r201 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 9 < 64 by decide))

theorem r202_mem : r202 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 10 < 64 by decide))

theorem r203_mem : r203 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 11 < 64 by decide))

theorem r204_mem : r204 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 12 < 64 by decide))

theorem r205_mem : r205 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 13 < 64 by decide))

theorem r206_mem : r206 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 14 < 64 by decide))

theorem r207_mem : r207 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 15 < 64 by decide))

theorem r208_mem : r208 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 16 < 64 by decide))

theorem r209_mem : r209 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 17 < 64 by decide))

theorem r210_mem : r210 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 18 < 64 by decide))

theorem r211_mem : r211 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 19 < 64 by decide))

theorem r212_mem : r212 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 20 < 64 by decide))

theorem r213_mem : r213 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 21 < 64 by decide))

theorem r214_mem : r214 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 22 < 64 by decide))

theorem r215_mem : r215 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 23 < 64 by decide))

theorem r216_mem : r216 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 24 < 64 by decide))

theorem r217_mem : r217 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 25 < 64 by decide))

theorem r218_mem : r218 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 26 < 64 by decide))

theorem r219_mem : r219 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 27 < 64 by decide))

theorem r220_mem : r220 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 28 < 64 by decide))

theorem r221_mem : r221 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 29 < 64 by decide))

theorem r222_mem : r222 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 30 < 64 by decide))

theorem r223_mem : r223 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 31 < 64 by decide))

theorem r224_mem : r224 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 32 < 64 by decide))

theorem r225_mem : r225 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 33 < 64 by decide))

theorem r226_mem : r226 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 34 < 64 by decide))

theorem r227_mem : r227 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 35 < 64 by decide))

theorem r228_mem : r228 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 36 < 64 by decide))

theorem r229_mem : r229 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 37 < 64 by decide))

theorem r230_mem : r230 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 38 < 64 by decide))

theorem r231_mem : r231 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 39 < 64 by decide))

theorem r232_mem : r232 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 40 < 64 by decide))

theorem r233_mem : r233 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 41 < 64 by decide))

theorem r234_mem : r234 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 42 < 64 by decide))

theorem r235_mem : r235 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 43 < 64 by decide))

theorem r236_mem : r236 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 44 < 64 by decide))

theorem r237_mem : r237 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 45 < 64 by decide))

theorem r238_mem : r238 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 46 < 64 by decide))

theorem r239_mem : r239 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 47 < 64 by decide))

theorem r240_mem : r240 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 48 < 64 by decide))

theorem r241_mem : r241 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 49 < 64 by decide))

theorem r242_mem : r242 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 50 < 64 by decide))

theorem r243_mem : r243 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 51 < 64 by decide))

theorem r244_mem : r244 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 52 < 64 by decide))

theorem r245_mem : r245 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 53 < 64 by decide))

theorem r246_mem : r246 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 54 < 64 by decide))

theorem r247_mem : r247 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 55 < 64 by decide))

theorem r248_mem : r248 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 56 < 64 by decide))

theorem r249_mem : r249 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 57 < 64 by decide))

theorem r250_mem : r250 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 58 < 64 by decide))

theorem r251_mem : r251 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 59 < 64 by decide))

theorem r252_mem : r252 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 60 < 64 by decide))

theorem r253_mem : r253 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 61 < 64 by decide))

theorem r254_mem : r254 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 62 < 64 by decide))

theorem r255_mem : r255 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk03) (show 63 < 64 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
