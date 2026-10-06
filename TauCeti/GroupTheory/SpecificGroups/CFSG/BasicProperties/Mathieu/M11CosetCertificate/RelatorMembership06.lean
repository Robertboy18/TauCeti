/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 06

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r384_mem : r384 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 0 < 64 by decide))

theorem r385_mem : r385 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 1 < 64 by decide))

theorem r386_mem : r386 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 2 < 64 by decide))

theorem r387_mem : r387 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 3 < 64 by decide))

theorem r388_mem : r388 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 4 < 64 by decide))

theorem r389_mem : r389 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 5 < 64 by decide))

theorem r390_mem : r390 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 6 < 64 by decide))

theorem r391_mem : r391 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 7 < 64 by decide))

theorem r392_mem : r392 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 8 < 64 by decide))

theorem r393_mem : r393 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 9 < 64 by decide))

theorem r394_mem : r394 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 10 < 64 by decide))

theorem r395_mem : r395 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 11 < 64 by decide))

theorem r396_mem : r396 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 12 < 64 by decide))

theorem r397_mem : r397 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 13 < 64 by decide))

theorem r398_mem : r398 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 14 < 64 by decide))

theorem r399_mem : r399 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 15 < 64 by decide))

theorem r400_mem : r400 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 16 < 64 by decide))

theorem r401_mem : r401 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 17 < 64 by decide))

theorem r402_mem : r402 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 18 < 64 by decide))

theorem r403_mem : r403 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 19 < 64 by decide))

theorem r404_mem : r404 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 20 < 64 by decide))

theorem r405_mem : r405 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 21 < 64 by decide))

theorem r406_mem : r406 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 22 < 64 by decide))

theorem r407_mem : r407 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 23 < 64 by decide))

theorem r408_mem : r408 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 24 < 64 by decide))

theorem r409_mem : r409 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 25 < 64 by decide))

theorem r410_mem : r410 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 26 < 64 by decide))

theorem r411_mem : r411 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 27 < 64 by decide))

theorem r412_mem : r412 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 28 < 64 by decide))

theorem r413_mem : r413 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 29 < 64 by decide))

theorem r414_mem : r414 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 30 < 64 by decide))

theorem r415_mem : r415 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 31 < 64 by decide))

theorem r416_mem : r416 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 32 < 64 by decide))

theorem r417_mem : r417 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 33 < 64 by decide))

theorem r418_mem : r418 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 34 < 64 by decide))

theorem r419_mem : r419 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 35 < 64 by decide))

theorem r420_mem : r420 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 36 < 64 by decide))

theorem r421_mem : r421 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 37 < 64 by decide))

theorem r422_mem : r422 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 38 < 64 by decide))

theorem r423_mem : r423 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 39 < 64 by decide))

theorem r424_mem : r424 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 40 < 64 by decide))

theorem r425_mem : r425 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 41 < 64 by decide))

theorem r426_mem : r426 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 42 < 64 by decide))

theorem r427_mem : r427 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 43 < 64 by decide))

theorem r428_mem : r428 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 44 < 64 by decide))

theorem r429_mem : r429 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 45 < 64 by decide))

theorem r430_mem : r430 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 46 < 64 by decide))

theorem r431_mem : r431 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 47 < 64 by decide))

theorem r432_mem : r432 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 48 < 64 by decide))

theorem r433_mem : r433 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 49 < 64 by decide))

theorem r434_mem : r434 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 50 < 64 by decide))

theorem r435_mem : r435 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 51 < 64 by decide))

theorem r436_mem : r436 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 52 < 64 by decide))

theorem r437_mem : r437 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 53 < 64 by decide))

theorem r438_mem : r438 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 54 < 64 by decide))

theorem r439_mem : r439 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 55 < 64 by decide))

theorem r440_mem : r440 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 56 < 64 by decide))

theorem r441_mem : r441 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 57 < 64 by decide))

theorem r442_mem : r442 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 58 < 64 by decide))

theorem r443_mem : r443 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 59 < 64 by decide))

theorem r444_mem : r444 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 60 < 64 by decide))

theorem r445_mem : r445 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 61 < 64 by decide))

theorem r446_mem : r446 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 62 < 64 by decide))

theorem r447_mem : r447 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk06) (show 63 < 64 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
