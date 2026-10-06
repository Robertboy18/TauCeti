/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Initial edges of the M11 coset certificate

Sixteen independent finite computations compare the literal initial bit masks
with the defining-word test for tree edges, covering all four letters and 990 points.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem initial_bits_00 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨0 + j.val, by omega⟩) =
      t :: table.word ⟨0 + j.val, by omega⟩) =
        bits000[t].testBit (0 + j.val) := by
  decide +kernel

theorem initial_bits_01 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨64 + j.val, by omega⟩) =
      t :: table.word ⟨64 + j.val, by omega⟩) =
        bits000[t].testBit (64 + j.val) := by
  decide +kernel

theorem initial_bits_02 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨128 + j.val, by omega⟩) =
      t :: table.word ⟨128 + j.val, by omega⟩) =
        bits000[t].testBit (128 + j.val) := by
  decide +kernel

theorem initial_bits_03 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨192 + j.val, by omega⟩) =
      t :: table.word ⟨192 + j.val, by omega⟩) =
        bits000[t].testBit (192 + j.val) := by
  decide +kernel

theorem initial_bits_04 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨256 + j.val, by omega⟩) =
      t :: table.word ⟨256 + j.val, by omega⟩) =
        bits000[t].testBit (256 + j.val) := by
  decide +kernel

theorem initial_bits_05 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨320 + j.val, by omega⟩) =
      t :: table.word ⟨320 + j.val, by omega⟩) =
        bits000[t].testBit (320 + j.val) := by
  decide +kernel

theorem initial_bits_06 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨384 + j.val, by omega⟩) =
      t :: table.word ⟨384 + j.val, by omega⟩) =
        bits000[t].testBit (384 + j.val) := by
  decide +kernel

theorem initial_bits_07 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨448 + j.val, by omega⟩) =
      t :: table.word ⟨448 + j.val, by omega⟩) =
        bits000[t].testBit (448 + j.val) := by
  decide +kernel

theorem initial_bits_08 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨512 + j.val, by omega⟩) =
      t :: table.word ⟨512 + j.val, by omega⟩) =
        bits000[t].testBit (512 + j.val) := by
  decide +kernel

theorem initial_bits_09 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨576 + j.val, by omega⟩) =
      t :: table.word ⟨576 + j.val, by omega⟩) =
        bits000[t].testBit (576 + j.val) := by
  decide +kernel

theorem initial_bits_10 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨640 + j.val, by omega⟩) =
      t :: table.word ⟨640 + j.val, by omega⟩) =
        bits000[t].testBit (640 + j.val) := by
  decide +kernel

theorem initial_bits_11 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨704 + j.val, by omega⟩) =
      t :: table.word ⟨704 + j.val, by omega⟩) =
        bits000[t].testBit (704 + j.val) := by
  decide +kernel

theorem initial_bits_12 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨768 + j.val, by omega⟩) =
      t :: table.word ⟨768 + j.val, by omega⟩) =
        bits000[t].testBit (768 + j.val) := by
  decide +kernel

theorem initial_bits_13 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨832 + j.val, by omega⟩) =
      t :: table.word ⟨832 + j.val, by omega⟩) =
        bits000[t].testBit (832 + j.val) := by
  decide +kernel

theorem initial_bits_14 : ∀ t : Fin 4, ∀ j : Fin 64,
    decide (table.word (table.act t ⟨896 + j.val, by omega⟩) =
      t :: table.word ⟨896 + j.val, by omega⟩) =
        bits000[t].testBit (896 + j.val) := by
  decide +kernel

theorem initial_bits_15 : ∀ t : Fin 4, ∀ j : Fin 30,
    decide (table.word (table.act t ⟨960 + j.val, by omega⟩) =
      t :: table.word ⟨960 + j.val, by omega⟩) =
        bits000[t].testBit (960 + j.val) := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
