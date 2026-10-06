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

/-- Trimmed scan word 384 holds in the exact presentation group. -/
theorem r384_eq_one : (r384.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    1 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 385 holds in the exact presentation group. -/
theorem r385_eq_one : (r385.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    3 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 386 holds in the exact presentation group. -/
theorem r386_eq_one : (r386.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    6 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 387 holds in the exact presentation group. -/
theorem r387_eq_one : (r387.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    7 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 388 holds in the exact presentation group. -/
theorem r388_eq_one : (r388.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    8 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 389 holds in the exact presentation group. -/
theorem r389_eq_one : (r389.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    9 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 390 holds in the exact presentation group. -/
theorem r390_eq_one : (r390.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    11 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 391 holds in the exact presentation group. -/
theorem r391_eq_one : (r391.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    12 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 392 holds in the exact presentation group. -/
theorem r392_eq_one : (r392.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    13 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 393 holds in the exact presentation group. -/
theorem r393_eq_one : (r393.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    14 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 394 holds in the exact presentation group. -/
theorem r394_eq_one : (r394.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    15 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 395 holds in the exact presentation group. -/
theorem r395_eq_one : (r395.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    0 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 396 holds in the exact presentation group. -/
theorem r396_eq_one : (r396.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    1 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 397 holds in the exact presentation group. -/
theorem r397_eq_one : (r397.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    2 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 398 holds in the exact presentation group. -/
theorem r398_eq_one : (r398.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    3 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 399 holds in the exact presentation group. -/
theorem r399_eq_one : (r399.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    4 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 400 holds in the exact presentation group. -/
theorem r400_eq_one : (r400.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    6 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 401 holds in the exact presentation group. -/
theorem r401_eq_one : (r401.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    7 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 402 holds in the exact presentation group. -/
theorem r402_eq_one : (r402.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    8 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 403 holds in the exact presentation group. -/
theorem r403_eq_one : (r403.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    9 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 404 holds in the exact presentation group. -/
theorem r404_eq_one : (r404.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    10 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 405 holds in the exact presentation group. -/
theorem r405_eq_one : (r405.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    11 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 406 holds in the exact presentation group. -/
theorem r406_eq_one : (r406.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    12 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 407 holds in the exact presentation group. -/
theorem r407_eq_one : (r407.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 false
    14 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 408 holds in the exact presentation group. -/
theorem r408_eq_one : (r408.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    0 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 409 holds in the exact presentation group. -/
theorem r409_eq_one : (r409.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    1 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 410 holds in the exact presentation group. -/
theorem r410_eq_one : (r410.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    2 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 411 holds in the exact presentation group. -/
theorem r411_eq_one : (r411.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    3 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 412 holds in the exact presentation group. -/
theorem r412_eq_one : (r412.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    4 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 413 holds in the exact presentation group. -/
theorem r413_eq_one : (r413.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    5 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 414 holds in the exact presentation group. -/
theorem r414_eq_one : (r414.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    6 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 415 holds in the exact presentation group. -/
theorem r415_eq_one : (r415.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    7 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 416 holds in the exact presentation group. -/
theorem r416_eq_one : (r416.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    8 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 417 holds in the exact presentation group. -/
theorem r417_eq_one : (r417.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    10 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 418 holds in the exact presentation group. -/
theorem r418_eq_one : (r418.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    11 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 419 holds in the exact presentation group. -/
theorem r419_eq_one : (r419.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    12 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 420 holds in the exact presentation group. -/
theorem r420_eq_one : (r420.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    13 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 421 holds in the exact presentation group. -/
theorem r421_eq_one : (r421.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word185 true
    14 word185_eq_one (by decide +kernel)

/-- Trimmed scan word 422 holds in the exact presentation group. -/
theorem r422_eq_one : (r422.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    0 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 423 holds in the exact presentation group. -/
theorem r423_eq_one : (r423.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    1 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 424 holds in the exact presentation group. -/
theorem r424_eq_one : (r424.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    2 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 425 holds in the exact presentation group. -/
theorem r425_eq_one : (r425.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    3 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 426 holds in the exact presentation group. -/
theorem r426_eq_one : (r426.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    4 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 427 holds in the exact presentation group. -/
theorem r427_eq_one : (r427.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    5 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 428 holds in the exact presentation group. -/
theorem r428_eq_one : (r428.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    6 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 429 holds in the exact presentation group. -/
theorem r429_eq_one : (r429.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    7 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 430 holds in the exact presentation group. -/
theorem r430_eq_one : (r430.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    8 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 431 holds in the exact presentation group. -/
theorem r431_eq_one : (r431.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    9 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 432 holds in the exact presentation group. -/
theorem r432_eq_one : (r432.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    10 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 433 holds in the exact presentation group. -/
theorem r433_eq_one : (r433.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    11 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 434 holds in the exact presentation group. -/
theorem r434_eq_one : (r434.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    12 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 435 holds in the exact presentation group. -/
theorem r435_eq_one : (r435.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    13 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 436 holds in the exact presentation group. -/
theorem r436_eq_one : (r436.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    14 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 437 holds in the exact presentation group. -/
theorem r437_eq_one : (r437.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 false
    15 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 438 holds in the exact presentation group. -/
theorem r438_eq_one : (r438.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    0 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 439 holds in the exact presentation group. -/
theorem r439_eq_one : (r439.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    1 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 440 holds in the exact presentation group. -/
theorem r440_eq_one : (r440.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    2 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 441 holds in the exact presentation group. -/
theorem r441_eq_one : (r441.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    3 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 442 holds in the exact presentation group. -/
theorem r442_eq_one : (r442.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    4 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 443 holds in the exact presentation group. -/
theorem r443_eq_one : (r443.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    5 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 444 holds in the exact presentation group. -/
theorem r444_eq_one : (r444.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    6 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 445 holds in the exact presentation group. -/
theorem r445_eq_one : (r445.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    7 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 446 holds in the exact presentation group. -/
theorem r446_eq_one : (r446.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    8 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 447 holds in the exact presentation group. -/
theorem r447_eq_one : (r447.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    9 word205_eq_one (by decide +kernel)

@[expose]
def scanBlock24 : List (List (Fin 4)) :=
  [r384, r385, r386, r387, r388,
    r389, r390, r391, r392, r393,
    r394, r395, r396, r397, r398,
    r399]

theorem scanBlock24_eq_one : ∀ w ∈ scanBlock24, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock24, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r384_eq_one
  · exact r385_eq_one
  · exact r386_eq_one
  · exact r387_eq_one
  · exact r388_eq_one
  · exact r389_eq_one
  · exact r390_eq_one
  · exact r391_eq_one
  · exact r392_eq_one
  · exact r393_eq_one
  · exact r394_eq_one
  · exact r395_eq_one
  · exact r396_eq_one
  · exact r397_eq_one
  · exact r398_eq_one
  · exact r399_eq_one

@[expose]
def scanBlock25 : List (List (Fin 4)) :=
  [r400, r401, r402, r403, r404,
    r405, r406, r407, r408, r409,
    r410, r411, r412, r413, r414,
    r415]

theorem scanBlock25_eq_one : ∀ w ∈ scanBlock25, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock25, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r400_eq_one
  · exact r401_eq_one
  · exact r402_eq_one
  · exact r403_eq_one
  · exact r404_eq_one
  · exact r405_eq_one
  · exact r406_eq_one
  · exact r407_eq_one
  · exact r408_eq_one
  · exact r409_eq_one
  · exact r410_eq_one
  · exact r411_eq_one
  · exact r412_eq_one
  · exact r413_eq_one
  · exact r414_eq_one
  · exact r415_eq_one

@[expose]
def scanBlock26 : List (List (Fin 4)) :=
  [r416, r417, r418, r419, r420,
    r421, r422, r423, r424, r425,
    r426, r427, r428, r429, r430,
    r431]

theorem scanBlock26_eq_one : ∀ w ∈ scanBlock26, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock26, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r416_eq_one
  · exact r417_eq_one
  · exact r418_eq_one
  · exact r419_eq_one
  · exact r420_eq_one
  · exact r421_eq_one
  · exact r422_eq_one
  · exact r423_eq_one
  · exact r424_eq_one
  · exact r425_eq_one
  · exact r426_eq_one
  · exact r427_eq_one
  · exact r428_eq_one
  · exact r429_eq_one
  · exact r430_eq_one
  · exact r431_eq_one

@[expose]
def scanBlock27 : List (List (Fin 4)) :=
  [r432, r433, r434, r435, r436,
    r437, r438, r439, r440, r441,
    r442, r443, r444, r445, r446,
    r447]

theorem scanBlock27_eq_one : ∀ w ∈ scanBlock27, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock27, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r432_eq_one
  · exact r433_eq_one
  · exact r434_eq_one
  · exact r435_eq_one
  · exact r436_eq_one
  · exact r437_eq_one
  · exact r438_eq_one
  · exact r439_eq_one
  · exact r440_eq_one
  · exact r441_eq_one
  · exact r442_eq_one
  · exact r443_eq_one
  · exact r444_eq_one
  · exact r445_eq_one
  · exact r446_eq_one
  · exact r447_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
