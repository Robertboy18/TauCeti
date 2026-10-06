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

/-- Trimmed scan word 448 holds in the exact presentation group. -/
theorem r448_eq_one : (r448.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    10 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 449 holds in the exact presentation group. -/
theorem r449_eq_one : (r449.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    11 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 450 holds in the exact presentation group. -/
theorem r450_eq_one : (r450.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    12 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 451 holds in the exact presentation group. -/
theorem r451_eq_one : (r451.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    13 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 452 holds in the exact presentation group. -/
theorem r452_eq_one : (r452.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    14 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 453 holds in the exact presentation group. -/
theorem r453_eq_one : (r453.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word205 true
    15 word205_eq_one (by decide +kernel)

/-- Trimmed scan word 454 holds in the exact presentation group. -/
theorem r454_eq_one : (r454.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    0 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 455 holds in the exact presentation group. -/
theorem r455_eq_one : (r455.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    1 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 456 holds in the exact presentation group. -/
theorem r456_eq_one : (r456.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    2 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 457 holds in the exact presentation group. -/
theorem r457_eq_one : (r457.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    3 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 458 holds in the exact presentation group. -/
theorem r458_eq_one : (r458.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    4 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 459 holds in the exact presentation group. -/
theorem r459_eq_one : (r459.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    5 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 460 holds in the exact presentation group. -/
theorem r460_eq_one : (r460.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    6 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 461 holds in the exact presentation group. -/
theorem r461_eq_one : (r461.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    7 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 462 holds in the exact presentation group. -/
theorem r462_eq_one : (r462.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    8 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 463 holds in the exact presentation group. -/
theorem r463_eq_one : (r463.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    9 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 464 holds in the exact presentation group. -/
theorem r464_eq_one : (r464.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    10 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 465 holds in the exact presentation group. -/
theorem r465_eq_one : (r465.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    11 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 466 holds in the exact presentation group. -/
theorem r466_eq_one : (r466.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    12 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 467 holds in the exact presentation group. -/
theorem r467_eq_one : (r467.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    13 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 468 holds in the exact presentation group. -/
theorem r468_eq_one : (r468.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 false
    14 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 469 holds in the exact presentation group. -/
theorem r469_eq_one : (r469.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    0 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 470 holds in the exact presentation group. -/
theorem r470_eq_one : (r470.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    1 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 471 holds in the exact presentation group. -/
theorem r471_eq_one : (r471.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    2 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 472 holds in the exact presentation group. -/
theorem r472_eq_one : (r472.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    3 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 473 holds in the exact presentation group. -/
theorem r473_eq_one : (r473.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    4 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 474 holds in the exact presentation group. -/
theorem r474_eq_one : (r474.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    5 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 475 holds in the exact presentation group. -/
theorem r475_eq_one : (r475.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    6 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 476 holds in the exact presentation group. -/
theorem r476_eq_one : (r476.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    7 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 477 holds in the exact presentation group. -/
theorem r477_eq_one : (r477.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    8 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 478 holds in the exact presentation group. -/
theorem r478_eq_one : (r478.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    9 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 479 holds in the exact presentation group. -/
theorem r479_eq_one : (r479.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    10 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 480 holds in the exact presentation group. -/
theorem r480_eq_one : (r480.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    11 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 481 holds in the exact presentation group. -/
theorem r481_eq_one : (r481.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    12 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 482 holds in the exact presentation group. -/
theorem r482_eq_one : (r482.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    13 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 483 holds in the exact presentation group. -/
theorem r483_eq_one : (r483.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word224 true
    14 word224_eq_one (by decide +kernel)

/-- Trimmed scan word 484 holds in the exact presentation group. -/
theorem r484_eq_one : (r484.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    0 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 485 holds in the exact presentation group. -/
theorem r485_eq_one : (r485.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    1 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 486 holds in the exact presentation group. -/
theorem r486_eq_one : (r486.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    2 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 487 holds in the exact presentation group. -/
theorem r487_eq_one : (r487.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    3 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 488 holds in the exact presentation group. -/
theorem r488_eq_one : (r488.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    4 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 489 holds in the exact presentation group. -/
theorem r489_eq_one : (r489.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    5 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 490 holds in the exact presentation group. -/
theorem r490_eq_one : (r490.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    6 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 491 holds in the exact presentation group. -/
theorem r491_eq_one : (r491.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    7 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 492 holds in the exact presentation group. -/
theorem r492_eq_one : (r492.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    8 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 493 holds in the exact presentation group. -/
theorem r493_eq_one : (r493.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    9 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 494 holds in the exact presentation group. -/
theorem r494_eq_one : (r494.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    10 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 495 holds in the exact presentation group. -/
theorem r495_eq_one : (r495.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    11 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 496 holds in the exact presentation group. -/
theorem r496_eq_one : (r496.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    12 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 497 holds in the exact presentation group. -/
theorem r497_eq_one : (r497.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    13 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 498 holds in the exact presentation group. -/
theorem r498_eq_one : (r498.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    14 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 499 holds in the exact presentation group. -/
theorem r499_eq_one : (r499.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 false
    15 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 500 holds in the exact presentation group. -/
theorem r500_eq_one : (r500.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    0 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 501 holds in the exact presentation group. -/
theorem r501_eq_one : (r501.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    1 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 502 holds in the exact presentation group. -/
theorem r502_eq_one : (r502.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    2 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 503 holds in the exact presentation group. -/
theorem r503_eq_one : (r503.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    3 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 504 holds in the exact presentation group. -/
theorem r504_eq_one : (r504.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    4 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 505 holds in the exact presentation group. -/
theorem r505_eq_one : (r505.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    5 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 506 holds in the exact presentation group. -/
theorem r506_eq_one : (r506.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    6 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 507 holds in the exact presentation group. -/
theorem r507_eq_one : (r507.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    7 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 508 holds in the exact presentation group. -/
theorem r508_eq_one : (r508.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    8 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 509 holds in the exact presentation group. -/
theorem r509_eq_one : (r509.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    9 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 510 holds in the exact presentation group. -/
theorem r510_eq_one : (r510.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    10 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 511 holds in the exact presentation group. -/
theorem r511_eq_one : (r511.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    11 word227_eq_one (by decide +kernel)

@[expose]
def scanBlock28 : List (List (Fin 4)) :=
  [r448, r449, r450, r451, r452,
    r453, r454, r455, r456, r457,
    r458, r459, r460, r461, r462,
    r463]

theorem scanBlock28_eq_one : ∀ w ∈ scanBlock28, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock28, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r448_eq_one
  · exact r449_eq_one
  · exact r450_eq_one
  · exact r451_eq_one
  · exact r452_eq_one
  · exact r453_eq_one
  · exact r454_eq_one
  · exact r455_eq_one
  · exact r456_eq_one
  · exact r457_eq_one
  · exact r458_eq_one
  · exact r459_eq_one
  · exact r460_eq_one
  · exact r461_eq_one
  · exact r462_eq_one
  · exact r463_eq_one

@[expose]
def scanBlock29 : List (List (Fin 4)) :=
  [r464, r465, r466, r467, r468,
    r469, r470, r471, r472, r473,
    r474, r475, r476, r477, r478,
    r479]

theorem scanBlock29_eq_one : ∀ w ∈ scanBlock29, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock29, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r464_eq_one
  · exact r465_eq_one
  · exact r466_eq_one
  · exact r467_eq_one
  · exact r468_eq_one
  · exact r469_eq_one
  · exact r470_eq_one
  · exact r471_eq_one
  · exact r472_eq_one
  · exact r473_eq_one
  · exact r474_eq_one
  · exact r475_eq_one
  · exact r476_eq_one
  · exact r477_eq_one
  · exact r478_eq_one
  · exact r479_eq_one

@[expose]
def scanBlock30 : List (List (Fin 4)) :=
  [r480, r481, r482, r483, r484,
    r485, r486, r487, r488, r489,
    r490, r491, r492, r493, r494,
    r495]

theorem scanBlock30_eq_one : ∀ w ∈ scanBlock30, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock30, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r480_eq_one
  · exact r481_eq_one
  · exact r482_eq_one
  · exact r483_eq_one
  · exact r484_eq_one
  · exact r485_eq_one
  · exact r486_eq_one
  · exact r487_eq_one
  · exact r488_eq_one
  · exact r489_eq_one
  · exact r490_eq_one
  · exact r491_eq_one
  · exact r492_eq_one
  · exact r493_eq_one
  · exact r494_eq_one
  · exact r495_eq_one

@[expose]
def scanBlock31 : List (List (Fin 4)) :=
  [r496, r497, r498, r499, r500,
    r501, r502, r503, r504, r505,
    r506, r507, r508, r509, r510,
    r511]

theorem scanBlock31_eq_one : ∀ w ∈ scanBlock31, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock31, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r496_eq_one
  · exact r497_eq_one
  · exact r498_eq_one
  · exact r499_eq_one
  · exact r500_eq_one
  · exact r501_eq_one
  · exact r502_eq_one
  · exact r503_eq_one
  · exact r504_eq_one
  · exact r505_eq_one
  · exact r506_eq_one
  · exact r507_eq_one
  · exact r508_eq_one
  · exact r509_eq_one
  · exact r510_eq_one
  · exact r511_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
