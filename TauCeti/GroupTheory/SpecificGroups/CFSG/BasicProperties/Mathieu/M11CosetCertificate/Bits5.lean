/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableBits

/-!
# M11 coset certificate: Bits5

Literal checkpoints: four natural-number masks at each stage.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def bits080row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbeffbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf6fffdff7ffed7fdbfffffffffabffffffffff * 2 ^ 480 +
  0x93edb77bdca1ffdfbfffbee8dfffe7eff7a37af7ffffdffe9eb7e7ff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits080row1 : ℕ :=
  0xfffffffffffffffffffffffffffffffffdffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffedba97fbfffffffbdffefffffffefffffbfbfffffffffffffff6ffff * 2 ^ 240 +
  0xbf237fd3ffeff5bfe7ffbffbffcdbef77fdbffbffff8fdfbffffffbf7f9f * 2 ^ 480 +
  0x8bf9ebfe6873f6ea9eecbbb2ffeffaf4fd07ff7fffebdecd10ffefffdbfe * 2 ^ 720 +
  0x252b29fb * 2 ^ 960

@[expose]
def bits080row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefff6fffbfff77feffffffffffffdfffff * 2 ^ 240 +
  0xff7fffffffd7feffbbffbffbfeff7ffbfbff777feff7d7efffafffffffff * 2 ^ 480 +
  0xfffdf21af9b13dd55fff7feff2fff7e9bbc9afdaf77f9dfcb1ffdfbdfbff * 2 ^ 720 +
  0x19ef6b67 * 2 ^ 960

@[expose]
def bits080row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffbfffffcb7effd75ffffb7b7ff7ffffffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfafd7d7d1ebdd6a7f7fbf3fffaf3ff7befdffdff77ffffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits080 : Vector ℕ 4 := #v[bits080row0, bits080row1, bits080row2, bits080row3]

@[expose]
def bits081row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbeffbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf6fffdff7ffed7fdbfffffffffabffffffffff * 2 ^ 480 +
  0x93edb77bdca1ffdfbfffbee8dfffe7eff7a37af7ffffdffe9eb7e7ff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits081row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffedfbd7fbffffffffdffefffffffefffffbfbfffffffffffffff7ffff * 2 ^ 240 +
  0xbf2f7fdbffeff5bfe7ffbffbffcdbff7ffdbffbffff8fdfbffffffffffbf * 2 ^ 480 +
  0x8ff9effe7873f6eabeecbbb2ffeffbf6fd27ff7fffebdecf10ffefffdbfe * 2 ^ 720 +
  0x252b29ff * 2 ^ 960

@[expose]
def bits081row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefff6fffbfff77ffffffffffffffffffff * 2 ^ 240 +
  0xff7fffffffd7feffbbffbffbfeff7ffbfbff777feff7d7efffafffffffff * 2 ^ 480 +
  0xfffdf21af9b13dd55fff7feff3fff7efbbc9afdaf77fddfcf5ffdfbdfbff * 2 ^ 720 +
  0x19ef6be7 * 2 ^ 960

@[expose]
def bits081row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffbfffffcb7effd75ffffb7b7ff7ffffffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfafd7d7d1ebdd6a7f7fbf3fffaf3ff7befdffdff77ffffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits081 : Vector ℕ 4 := #v[bits081row0, bits081row1, bits081row2, bits081row3]

@[expose]
def bits082row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbeffbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf6fffdff7ffed7fdbfffffffffabffffffffff * 2 ^ 480 +
  0x93edb77bdca1ffdfbfffbee8dfffe7eff7a37af7ffffdffe9eb7e7ff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits082row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffeffbd7fffffffffffffffffffffffffffffbfffffffffffffff7ffff * 2 ^ 240 +
  0xff2f7fdffffff5bfe7ffbffbffcfbfffffffffbffffcfdfbffffffffffbf * 2 ^ 480 +
  0x8ffbeffe7973ffeabeecbbb6ffeffbfeff37ffffffebdfff57ffffffdbfe * 2 ^ 720 +
  0x253b29ff * 2 ^ 960

@[expose]
def bits082row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefff6fffbfff77ffffffffffffffffffff * 2 ^ 240 +
  0xff7fffffffd7feffbbffbffbfeff7ffbfbff777feff7d7efffafffffffff * 2 ^ 480 +
  0xfffdf21af9b13dd55fff7feff3fff7efbbc9afdaf77fddfcf5ffdfbdfbff * 2 ^ 720 +
  0x19ef6be7 * 2 ^ 960

@[expose]
def bits082row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffbfffffcb7effd75ffffb7b7ff7ffffffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfafd7d7d1ebdd6a7f7fbf3fffaf3ff7befdffdff77ffffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits082 : Vector ℕ 4 := #v[bits082row0, bits082row1, bits082row2, bits082row3]

@[expose]
def bits083row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffffefffefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf7ffffffffffd7ffbfffffffffebffffffffff * 2 ^ 480 +
  0x93fdf77bdce9ffdfffffbee9dfffe7fff7a3faf7fffffffe9ebfefff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits083row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffefffd7fffffffffffffffffffffffffffffbfffffffffffffff7ffff * 2 ^ 240 +
  0xff2fffdffffff5bfefffbffbffdfffffffffffbffffcfdfbffffffffffbf * 2 ^ 480 +
  0x8fffeffe7973ffebfeecbfb6fffffbfeffb7ffffffebdfff57fffffffbfe * 2 ^ 720 +
  0x253b39ff * 2 ^ 960

@[expose]
def bits083row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefff6fffbfff77ffffffffffffffffffff * 2 ^ 240 +
  0xff7fffffffd7feffbbffbffbfeff7ffbfbff777feff7d7efffafffffffff * 2 ^ 480 +
  0xfffdf21af9b13dd55fff7feff3fff7efbbc9afdaf77fddfcf5ffdfbdfbff * 2 ^ 720 +
  0x19ef6be7 * 2 ^ 960

@[expose]
def bits083row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffbfffffcb7effd75ffffb7b7ff7ffffffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfafd7d7d1ebdd6a7f7fbf3fffaf3ff7befdffdff77ffffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits083 : Vector ℕ 4 := #v[bits083row0, bits083row1, bits083row2, bits083row3]

@[expose]
def bits084row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffffefffefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf7ffffffffffd7ffbfffffffffebffffffffff * 2 ^ 480 +
  0x93fdf77bdce9ffdfffffbee9dfffe7fff7a3faf7fffffffe9ebfefff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits084row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffefffd7fffffffffffffffffffffffffffffbfffffffffffffff7ffff * 2 ^ 240 +
  0xffbfffdffffff5bfefffbffbffdfffffffffffbffffcfdffffffffffffbf * 2 ^ 480 +
  0x8fffeffe797bffebfeefbfbefffffbffffb7fffffffbffff57fffffffffe * 2 ^ 720 +
  0x253b39ff * 2 ^ 960

@[expose]
def bits084row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefffefffbffff7ffffffffffffffffffff * 2 ^ 240 +
  0xff7fffffffd7feffbbfffffbfffffffbfbff777fefffdfffffafffffffff * 2 ^ 480 +
  0xfffdf21af9b1fdd57ffffffff3fff7efbfc9afdaf77fddfdf7ffffffffff * 2 ^ 720 +
  0x19ef6bef * 2 ^ 960

@[expose]
def bits084row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffbfffffcb7effd75ffffb7b7ff7ffffffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfafd7d7d1ebdd6a7f7fbf3fffaf3ff7befdffdff77ffffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits084 : Vector ℕ 4 := #v[bits084row0, bits084row1, bits084row2, bits084row3]

@[expose]
def bits085row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffffffffefef7fffffffffffffffffffff7fffffbfffffffff7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7ffffffbdffffffffffffd7ffbffffffffffbffffffffff * 2 ^ 480 +
  0x93fdf77bdce9ffdfffffbee9ffffe7fff7b3faffffffffff9fffefff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits085row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffefffd7fffffffffffffffffffffffffffffbfffffffffffffff7ffff * 2 ^ 240 +
  0xffbfffdffffff5bfefffbffbffdfffffffffffbffffcfdffffffffffffbf * 2 ^ 480 +
  0x8fffeffe797bffebfeefbfbefffffbffffb7fffffffbffff57fffffffffe * 2 ^ 720 +
  0x253b39ff * 2 ^ 960

@[expose]
def bits085row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefffefffbffff7ffffffffffffffffffff * 2 ^ 240 +
  0xff7fffffffd7fefffffffffbfffffffbfbff777fffffffffffafffffffff * 2 ^ 480 +
  0xfffdf37bf9f5fdfdfffffffff7fff7ffffc9efdaf77fddfdf7ffffffffff * 2 ^ 720 +
  0x39ef6fef * 2 ^ 960

@[expose]
def bits085row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffbfffffcb7effd75ffffb7b7ff7ffffffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfafd7d7d1ebdd6a7f7fbf3fffaf3ff7befdffdff77ffffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits085 : Vector ℕ 4 := #v[bits085row0, bits085row1, bits085row2, bits085row3]

@[expose]
def bits086row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffffffffefefffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffdf7fffff7fffffffffdfffffffffffffffffffffffffffbffffffffff * 2 ^ 480 +
  0xdbfdfffbfdf9ffdfffffbffdfffff7fffff7fbffffffffffdfffffffffff * 2 ^ 720 +
  0x2f6fdd7f * 2 ^ 960

@[expose]
def bits086row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffefffd7fffffffffffffffffffffffffffffbfffffffffffffff7ffff * 2 ^ 240 +
  0xffbfffdffffff5bfefffbffbffdfffffffffffbffffcfdffffffffffffbf * 2 ^ 480 +
  0x8fffeffe797bffebfeefbfbefffffbffffb7fffffffbffff57fffffffffe * 2 ^ 720 +
  0x253b39ff * 2 ^ 960

@[expose]
def bits086row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefffefffbffff7ffffffffffffffffffff * 2 ^ 240 +
  0xff7fffffffd7fefffffffffbfffffffbfbff777fffffffffffafffffffff * 2 ^ 480 +
  0xfffdf37bf9f5fdfdfffffffff7fff7ffffc9efdaf77fddfdf7ffffffffff * 2 ^ 720 +
  0x39ef6fef * 2 ^ 960

@[expose]
def bits086row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffbfffffcb7effd75ffffb7b7ff7ffffffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfafd7d7d1ebdd6a7f7fbf3fffaf3ff7befdffdff77ffffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits086 : Vector ℕ 4 := #v[bits086row0, bits086row1, bits086row2, bits086row3]

@[expose]
def bits087row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffffffffefefffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffdf7fffff7fffffffffdfffffffffffffffffffffffffffbffffffffff * 2 ^ 480 +
  0xdbfdfffbfdf9ffdfffffbffdfffff7fffff7fbffffffffffdfffffffffff * 2 ^ 720 +
  0x2f6fdd7f * 2 ^ 960

@[expose]
def bits087row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffefffd7fffffffffffffffffffffffffffffbfffffffffffffff7ffff * 2 ^ 240 +
  0xffbfffdffffff5bfefffbffbffdfffffffffffbffffcfdffffffffffffbf * 2 ^ 480 +
  0x8fffeffe797bffebfeefbfbefffffbffffb7fffffffbffff57fffffffffe * 2 ^ 720 +
  0x253b39ff * 2 ^ 960

@[expose]
def bits087row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefffefffbffff7ffffffffffffffffffff * 2 ^ 240 +
  0xff7fffffffd7fefffffffffbfffffffbfbff777fffffffffffafffffffff * 2 ^ 480 +
  0xfffdf37bf9f5fdfdfffffffff7fff7ffffc9efdaf77fddfdf7ffffffffff * 2 ^ 720 +
  0x39ef6fef * 2 ^ 960

@[expose]
def bits087row3 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffbfffffdf7ffff75ffffb7b7ff7fffffffffffffffdfffdffffebfffff * 2 ^ 480 +
  0xdf7fe7bbfafdff7f9ebfd6bff7fbf3fffaf3fffffffffdff7fffffffffff * 2 ^ 720 +
  0x29ff3eff * 2 ^ 960

@[expose]
def bits087 : Vector ℕ 4 := #v[bits087row0, bits087row1, bits087row2, bits087row3]

@[expose]
def bits088row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffffffffefefffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffdf7fffff7fffffffffdfffffffffffffffffffffffffffbffffffffff * 2 ^ 480 +
  0xdbfdfffbfdf9ffdfffffbffdfffff7fffff7fbffffffffffdfffffffffff * 2 ^ 720 +
  0x2f6fdd7f * 2 ^ 960

@[expose]
def bits088row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffefffd7fffffffffffffffffffffffffffffbfffffffffffffff7ffff * 2 ^ 240 +
  0xffbfffdffffff5bfefffbffbffdfffffffffffbffffcfdffffffffffffbf * 2 ^ 480 +
  0x8fffeffe797bffebfeefbfbefffffbffffb7fffffffbffff57fffffffffe * 2 ^ 720 +
  0x253b39ff * 2 ^ 960

@[expose]
def bits088row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffbffffffffffffffffffefffefffffffffffffffffffffffffffff * 2 ^ 240 +
  0xff7ffffffffffefffffffffbfffffffbffff7f7fffffffffffefffffffff * 2 ^ 480 +
  0xfffffb7bfdf5fdfffffffffffffff7ffffcdfffaf77fddfdf7ffffffffff * 2 ^ 720 +
  0x39ef6fef * 2 ^ 960

@[expose]
def bits088row3 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7ffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffffffffdf7ffff75ffffb7b7ffffffffffffffffffffffdfffffffffff * 2 ^ 480 +
  0xdfffe7fbfafdffffbfffdebffffbf7fffbf3ffffffffffff7fffffffffff * 2 ^ 720 +
  0x29ff3eff * 2 ^ 960

@[expose]
def bits088 : Vector ℕ 4 := #v[bits088row0, bits088row1, bits088row2, bits088row3]

@[expose]
def bits089row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffffffffefefffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffdf7fffff7fffffffffdfffffffffffffffffffffffffffbffffffffff * 2 ^ 480 +
  0xdbfdfffbfdf9ffdfffffbffdfffff7fffff7fbffffffffffdfffffffffff * 2 ^ 720 +
  0x2f6fdd7f * 2 ^ 960

@[expose]
def bits089row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffefffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffbfffdffffff5bfefffffffffdfffffffffffbffffcffffffffffffffbf * 2 ^ 480 +
  0x8fffeffe797bffebfeefbfbefffffbffffb7fffffffbffff57fffffffffe * 2 ^ 720 +
  0x253b39ff * 2 ^ 960

@[expose]
def bits089row2 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xfffffffffffffffffffffffffffffffbffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffff7ffff5fdfffffffffffffff7fffffffffffffffffdffffffffffff * 2 ^ 720 +
  0x3defffef * 2 ^ 960

@[expose]
def bits089row3 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7ffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffffffffdf7ffff75ffffb7b7ffffffffffffffffffffffdfffffffffff * 2 ^ 480 +
  0xdfffe7fbfafdffffbfffdebffffbf7fffbf3ffffffffffff7fffffffffff * 2 ^ 720 +
  0x29ff3eff * 2 ^ 960

@[expose]
def bits089 : Vector ℕ 4 := #v[bits089row0, bits089row1, bits089row2, bits089row3]

@[expose]
def bits090row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffffffffefefffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffdf7fffff7fffffffffdfffffffffffffffffffffffffffbffffffffff * 2 ^ 480 +
  0xdbfdfffbfdf9ffdfffffbffdfffff7fffff7fbffffffffffdfffffffffff * 2 ^ 720 +
  0x2f6fdd7f * 2 ^ 960

@[expose]
def bits090row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffbf * 2 ^ 480 +
  0xdfffefff7f7fffffffffffbffffffbfffff7fffffffffffff7ffffffffff * 2 ^ 720 +
  0x25bf7fff * 2 ^ 960

@[expose]
def bits090row2 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xfffffffffffffffffffffffffffffffbffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffff7ffff5fdfffffffffffffff7fffffffffffffffffdffffffffffff * 2 ^ 720 +
  0x3defffef * 2 ^ 960

@[expose]
def bits090row3 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7ffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffffffffdf7ffff75ffffb7b7ffffffffffffffffffffffdfffffffffff * 2 ^ 480 +
  0xdfffe7fbfafdffffbfffdebffffbf7fffbf3ffffffffffff7fffffffffff * 2 ^ 720 +
  0x29ff3eff * 2 ^ 960

@[expose]
def bits090 : Vector ℕ 4 := #v[bits090row0, bits090row1, bits090row2, bits090row3]

@[expose]
def bits091row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffffffffefefffffffffffffffffffffffffffffffffffffff7ffff * 2 ^ 240 +
  0xfffdf7fffff7fffffffffdfffffffffffffffffffffffffffbffffffffff * 2 ^ 480 +
  0xdbfdfffbfdf9ffdfffffbffdfffff7fffff7fbffffffffffdfffffffffff * 2 ^ 720 +
  0x2f6fdd7f * 2 ^ 960

@[expose]
def bits091row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffff * 2 ^ 720 +
  0x27ffffff * 2 ^ 960

@[expose]
def bits091row2 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffff7ffff7fdfffffffffffffff7fffffffffffffffffdffffffffffff * 2 ^ 720 +
  0x3defffff * 2 ^ 960

@[expose]
def bits091row3 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xfffffffffff7fffff7ffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xdfffe7fffefdffffffffffbffffbf7fffbf3ffffffffffff7fffffffffff * 2 ^ 720 +
  0x29ff3eff * 2 ^ 960

@[expose]
def bits091 : Vector ℕ 4 := #v[bits091row0, bits091row1, bits091row2, bits091row3]

@[expose]
def bits092row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffffffffffeffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xfffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xfffffffbfdf9ffdffffffffdfffffffffffffbffffffffffffffffffffff * 2 ^ 720 +
  0x2f6fff7f * 2 ^ 960

@[expose]
def bits092row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffff * 2 ^ 720 +
  0x27ffffff * 2 ^ 960

@[expose]
def bits092row2 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffff7ffff7fdfffffffffffffff7fffffffffffffffffdffffffffffff * 2 ^ 720 +
  0x3defffff * 2 ^ 960

@[expose]
def bits092row3 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xfffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xdfffffffffffffffffffffbfffffffffffffffffffffffffffffffffffff * 2 ^ 720 +
  0x3fffffff * 2 ^ 960

@[expose]
def bits092 : Vector ℕ 4 := #v[bits092row0, bits092row1, bits092row2, bits092row3]

@[expose]
def bits093row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 720 +
  0x3fffffff * 2 ^ 960

@[expose]
def bits093row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 720 +
  0x3fffffff * 2 ^ 960

@[expose]
def bits093row2 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 720 +
  0x3fffffff * 2 ^ 960

@[expose]
def bits093row3 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 240 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 480 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 720 +
  0x3fffffff * 2 ^ 960

@[expose]
def bits093 : Vector ℕ 4 := #v[bits093row0, bits093row1, bits093row2, bits093row3]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
