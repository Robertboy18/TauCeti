/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableFast

/-!
# M11 coset certificate: Relators0

Literal scan words, indexed in the order used by the certificate.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def r0 : List (Fin 4) := [0, 2]

@[expose]
def r1 : List (Fin 4) := [1, 3]

@[expose]
def r2 : List (Fin 4) := [2, 0]

@[expose]
def r3 : List (Fin 4) := [3, 1]

@[expose]
def r4 : List (Fin 4) := [0, 0, 0, 3, 3, 3, 3, 0, 3]

@[expose]
def r5 : List (Fin 4) := [0, 0, 3, 3, 3, 3, 0, 3, 0]

@[expose]
def r6 : List (Fin 4) := [3, 3, 3, 3, 0, 3, 0, 0, 0]

@[expose]
def r7 : List (Fin 4) := [3, 3, 3, 0, 3, 0, 0, 0, 3]

@[expose]
def r8 : List (Fin 4) := [3, 3, 0, 3, 0, 0, 0, 3, 3]

@[expose]
def r9 : List (Fin 4) := [3, 0, 3, 0, 0, 0, 3, 3, 3]

@[expose]
def r10 : List (Fin 4) := [0, 3, 0, 0, 0, 3, 3, 3, 3]

@[expose]
def r11 : List (Fin 4) := [3, 0, 0, 0, 3, 3, 3, 3, 0]

@[expose]
def r12 : List (Fin 4) := [1, 2, 1, 1, 1, 1, 2, 2, 2]

@[expose]
def r13 : List (Fin 4) := [2, 1, 1, 1, 1, 2, 2, 2, 1]

@[expose]
def r14 : List (Fin 4) := [1, 1, 1, 1, 2, 2, 2, 1, 2]

@[expose]
def r15 : List (Fin 4) := [1, 1, 1, 2, 2, 2, 1, 2, 1]

@[expose]
def r16 : List (Fin 4) := [1, 1, 2, 2, 2, 1, 2, 1, 1]

@[expose]
def r17 : List (Fin 4) := [1, 2, 2, 2, 1, 2, 1, 1, 1]

@[expose]
def r18 : List (Fin 4) := [2, 2, 2, 1, 2, 1, 1, 1, 1]

@[expose]
def r19 : List (Fin 4) := [2, 2, 1, 2, 1, 1, 1, 1, 2]

@[expose]
def r20 : List (Fin 4) := [2, 1, 2, 1, 1, 1, 1, 2, 2]

@[expose]
def r21 : List (Fin 4) := [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]

@[expose]
def r22 : List (Fin 4) := [1, 0, 1, 2, 3, 2, 1, 2, 3, 0]

@[expose]
def r23 : List (Fin 4) := [0, 1, 2, 3, 2, 1, 2, 3, 0, 1]

@[expose]
def r24 : List (Fin 4) := [1, 2, 3, 2, 1, 2, 3, 0, 1, 0]

@[expose]
def r25 : List (Fin 4) := [2, 3, 2, 1, 2, 3, 0, 1, 0, 1]

@[expose]
def r26 : List (Fin 4) := [3, 2, 1, 2, 3, 0, 1, 0, 1, 2]

@[expose]
def r27 : List (Fin 4) := [2, 1, 2, 3, 0, 1, 0, 1, 2, 3]

@[expose]
def r28 : List (Fin 4) := [1, 2, 3, 0, 1, 0, 1, 2, 3, 2]

@[expose]
def r29 : List (Fin 4) := [2, 3, 0, 1, 0, 1, 2, 3, 2, 1]

@[expose]
def r30 : List (Fin 4) := [3, 0, 1, 0, 1, 2, 3, 2, 1, 2]

@[expose]
def r31 : List (Fin 4) := [1, 0, 3, 0, 1, 0, 3, 2, 3, 2]

@[expose]
def r32 : List (Fin 4) := [0, 3, 0, 1, 0, 3, 2, 3, 2, 1]

@[expose]
def r33 : List (Fin 4) := [3, 0, 1, 0, 3, 2, 3, 2, 1, 0]

@[expose]
def r34 : List (Fin 4) := [0, 1, 0, 3, 2, 3, 2, 1, 0, 3]

@[expose]
def r35 : List (Fin 4) := [1, 0, 3, 2, 3, 2, 1, 0, 3, 0]

@[expose]
def r36 : List (Fin 4) := [0, 3, 2, 3, 2, 1, 0, 3, 0, 1]

@[expose]
def r37 : List (Fin 4) := [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]

@[expose]
def r38 : List (Fin 4) := [2, 3, 2, 1, 0, 3, 0, 1, 0, 3]

@[expose]
def r39 : List (Fin 4) := [3, 2, 1, 0, 3, 0, 1, 0, 3, 2]

@[expose]
def r40 : List (Fin 4) := [2, 1, 0, 3, 0, 1, 0, 3, 2, 3]

@[expose]
def r41 : List (Fin 4) := [0, 3, 3, 3, 2, 1, 1, 1, 1, 2, 2, 3, 0, 0]

@[expose]
def r42 : List (Fin 4) := [3, 3, 2, 1, 1, 1, 1, 2, 2, 3, 0, 0, 0, 3]

@[expose]
def r43 : List (Fin 4) := [1, 1, 1, 1, 2, 2, 3, 0, 0, 0, 3, 3, 3, 2]

@[expose]
def r44 : List (Fin 4) := [1, 1, 1, 2, 2, 3, 0, 0, 0, 3, 3, 3, 2, 1]

@[expose]
def r45 : List (Fin 4) := [2, 2, 3, 0, 0, 0, 3, 3, 3, 2, 1, 1, 1, 1]

@[expose]
def r46 : List (Fin 4) := [2, 3, 0, 0, 0, 3, 3, 3, 2, 1, 1, 1, 1, 2]

@[expose]
def r47 : List (Fin 4) := [0, 0, 3, 3, 3, 3, 0, 1, 1, 1, 2, 2, 2, 1]

@[expose]
def r48 : List (Fin 4) := [3, 3, 3, 0, 1, 1, 1, 2, 2, 2, 1, 0, 0, 3]

@[expose]
def r49 : List (Fin 4) := [3, 3, 0, 1, 1, 1, 2, 2, 2, 1, 0, 0, 3, 3]

@[expose]
def r50 : List (Fin 4) := [3, 0, 1, 1, 1, 2, 2, 2, 1, 0, 0, 3, 3, 3]

@[expose]
def r51 : List (Fin 4) := [1, 1, 2, 2, 2, 1, 0, 0, 3, 3, 3, 3, 0, 1]

@[expose]
def r52 : List (Fin 4) := [1, 2, 1, 0, 0, 0, 3, 3, 3, 3, 0, 1, 1, 2, 2, 2]

@[expose]
def r53 : List (Fin 4) := [0, 3, 3, 3, 3, 0, 1, 1, 2, 2, 2, 1, 2, 1, 0, 0]

@[expose]
def r54 : List (Fin 4) := [0, 0, 0, 1, 2, 2, 2, 1, 2, 3, 0, 3]

@[expose]
def r55 : List (Fin 4) := [1, 2, 2, 2, 1, 2, 3, 0, 3, 0, 0, 0]

@[expose]
def r56 : List (Fin 4) := [2, 2, 2, 1, 2, 3, 0, 3, 0, 0, 0, 1]

@[expose]
def r57 : List (Fin 4) := [1, 2, 3, 0, 3, 0, 0, 0, 1, 2, 2, 2]

@[expose]
def r58 : List (Fin 4) := [2, 3, 0, 3, 0, 0, 0, 1, 2, 2, 2, 1]

@[expose]
def r59 : List (Fin 4) := [1, 2, 1, 0, 3, 0, 0, 0, 3, 2, 2, 2]

@[expose]
def r60 : List (Fin 4) := [0, 0, 0, 3, 2, 2, 2, 1, 2, 1, 0, 3]

@[expose]
def r61 : List (Fin 4) := [0, 3, 2, 2, 2, 1, 2, 1, 0, 3, 0, 0]

@[expose]
def r62 : List (Fin 4) := [3, 2, 2, 2, 1, 2, 1, 0, 3, 0, 0, 0]

@[expose]
def r63 : List (Fin 4) := [2, 2, 2, 1, 2, 1, 0, 3, 0, 0, 0, 3]

@[expose]
def r64 : List (Fin 4) := [2, 2, 1, 2, 1, 0, 3, 0, 0, 0, 3, 2]

@[expose]
def r65 : List (Fin 4) := [2, 1, 2, 1, 0, 3, 0, 0, 0, 3, 2, 2]

@[expose]
def r66 : List (Fin 4) := [0, 0, 0, 1, 1, 2, 2, 2, 1, 2, 3, 3, 0, 3]

@[expose]
def r67 : List (Fin 4) := [0, 1, 1, 2, 2, 2, 1, 2, 3, 3, 0, 3, 0, 0]

@[expose]
def r68 : List (Fin 4) := [3, 3, 0, 3, 0, 0, 0, 1, 1, 2, 2, 2, 1, 2]

@[expose]
def r69 : List (Fin 4) := [1, 0, 3, 0, 0, 0, 3, 3, 2, 2, 2, 1, 2, 1]

@[expose]
def r70 : List (Fin 4) := [0, 3, 0, 0, 0, 3, 3, 2, 2, 2, 1, 2, 1, 1]

@[expose]
def r71 : List (Fin 4) := [0, 0, 3, 3, 2, 2, 2, 1, 2, 1, 1, 0, 3, 0]

@[expose]
def r72 : List (Fin 4) := [3, 3, 3, 3, 2, 1, 2, 1, 1, 1, 1, 2, 3, 0, 0, 0]

@[expose]
def r73 : List (Fin 4) := [1, 1, 1, 2, 3, 0, 0, 0, 3, 3, 3, 3, 2, 1, 2, 1]

@[expose]
def r74 : List (Fin 4) := [1, 1, 2, 3, 0, 0, 0, 3, 3, 3, 3, 2, 1, 2, 1, 1]

@[expose]
def r75 : List (Fin 4) := [0, 3, 3, 3, 3, 0, 3, 0, 1, 1, 1, 1, 2, 2, 2, 1]

@[expose]
def r76 : List (Fin 4) := [3, 3, 3, 0, 3, 0, 1, 1, 1, 1, 2, 2, 2, 1, 0, 3]

@[expose]
def r77 : List (Fin 4) := [3, 0, 3, 0, 1, 1, 1, 1, 2, 2, 2, 1, 0, 3, 3, 3]

@[expose]
def r78 : List (Fin 4) := [2, 2, 3, 3, 3, 3, 0, 3, 0, 0, 1, 2, 1, 1, 1, 1]

@[expose]
def r79 : List (Fin 4) := [1, 1, 1, 0, 0, 3, 3, 3, 3, 0, 3, 2, 2, 1, 2, 1]

@[expose]
def r80 : List (Fin 4) := [0, 0, 3, 3, 3, 3, 2, 2, 1, 2, 1, 1, 1, 0]

@[expose]
def r81 : List (Fin 4) := [1, 1, 0, 0, 0, 3, 3, 3, 3, 2, 2, 1, 2, 1]

@[expose]
def r82 : List (Fin 4) := [3, 3, 0, 3, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3]

@[expose]
def r83 : List (Fin 4) := [2, 2, 3, 3, 3, 0, 3, 0, 0, 1, 1, 1, 1, 2]

@[expose]
def r84 : List (Fin 4) := [2, 3, 3, 3, 0, 3, 0, 0, 1, 1, 1, 1, 2, 2]

@[expose]
def r85 : List (Fin 4) := [2, 1, 2, 1, 1, 1, 1, 0, 3, 3, 3, 3, 0, 3]

@[expose]
def r86 : List (Fin 4) := [0, 3, 3, 3, 3, 3, 2, 1, 2, 3, 0, 1, 0, 0, 0]

@[expose]
def r87 : List (Fin 4) := [3, 3, 3, 3, 3, 2, 1, 2, 3, 0, 1, 0, 0, 0, 0]

@[expose]
def r88 : List (Fin 4) := [2, 1, 2, 3, 0, 1, 0, 0, 0, 0, 3, 3, 3, 3, 3]

@[expose]
def r89 : List (Fin 4) := [1, 2, 3, 0, 1, 0, 0, 0, 0, 3, 3, 3, 3, 3, 2]

@[expose]
def r90 : List (Fin 4) := [2, 3, 0, 1, 0, 0, 0, 0, 3, 3, 3, 3, 3, 2, 1]

@[expose]
def r91 : List (Fin 4) := [3, 0, 1, 0, 0, 0, 0, 3, 3, 3, 3, 3, 2, 1, 2]

@[expose]
def r92 : List (Fin 4) := [1, 0, 3, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2]

@[expose]
def r93 : List (Fin 4) := [1, 2, 2, 2, 2, 3, 2, 1, 0, 3, 0, 1, 1, 1, 1]

@[expose]
def r94 : List (Fin 4) := [2, 2, 2, 2, 3, 2, 1, 0, 3, 0, 1, 1, 1, 1, 1]

@[expose]
def r95 : List (Fin 4) := [0, 0, 3, 2, 1, 2, 3, 0, 1, 0, 3, 3, 3, 0, 3]

@[expose]
def r96 : List (Fin 4) := [3, 0, 1, 0, 3, 3, 3, 0, 3, 0, 0, 3, 2, 1, 2]

@[expose]
def r97 : List (Fin 4) := [0, 1, 0, 3, 3, 3, 0, 3, 0, 0, 3, 2, 1, 2, 3]

@[expose]
def r98 : List (Fin 4) := [0, 3, 0, 0, 3, 2, 1, 2, 3, 0, 1, 0, 3, 3, 3]

@[expose]
def r99 : List (Fin 4) := [2, 1, 1, 1, 2, 3, 2, 1, 0, 3, 0, 1, 2, 2, 1]

@[expose]
def r100 : List (Fin 4) := [2, 1, 0, 3, 0, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3]

@[expose]
def r101 : List (Fin 4) := [0, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 0, 3]

@[expose]
def r102 : List (Fin 4) := [2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 0, 3, 0, 1, 2]

@[expose]
def r103 : List (Fin 4) := [0, 0, 3, 0, 1, 0, 3, 2, 3, 0, 0, 3, 3, 3, 3]

@[expose]
def r104 : List (Fin 4) := [1, 0, 3, 2, 3, 0, 0, 3, 3, 3, 3, 0, 0, 3, 0]

@[expose]
def r105 : List (Fin 4) := [0, 3, 2, 3, 0, 0, 3, 3, 3, 3, 0, 0, 3, 0, 1]

@[expose]
def r106 : List (Fin 4) := [3, 2, 3, 0, 0, 3, 3, 3, 3, 0, 0, 3, 0, 1, 0]

@[expose]
def r107 : List (Fin 4) := [1, 0, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2]

@[expose]
def r108 : List (Fin 4) := [2, 3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 0, 1]

@[expose]
def r109 : List (Fin 4) := [3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 0, 1, 2]

@[expose]
def r110 : List (Fin 4) := [2, 1, 1, 1, 1, 2, 2, 1, 0, 1, 2, 3, 2, 1, 2]

@[expose]
def r111 : List (Fin 4) := [0, 0, 3, 3, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0]

@[expose]
def r112 : List (Fin 4) := [0, 3, 3, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 0]

@[expose]
def r113 : List (Fin 4) := [1, 0, 3, 2, 3, 3, 0, 0, 0, 3, 3, 3, 0, 3, 0]

@[expose]
def r114 : List (Fin 4) := [0, 3, 2, 3, 3, 0, 0, 0, 3, 3, 3, 0, 3, 0, 1]

@[expose]
def r115 : List (Fin 4) := [3, 2, 3, 3, 0, 0, 0, 3, 3, 3, 0, 3, 0, 1, 0]

@[expose]
def r116 : List (Fin 4) := [3, 3, 0, 0, 0, 3, 3, 3, 0, 3, 0, 1, 0, 3, 2]

@[expose]
def r117 : List (Fin 4) := [1, 0, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1]

@[expose]
def r118 : List (Fin 4) := [1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 0]

@[expose]
def r119 : List (Fin 4) := [2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1]

@[expose]
def r120 : List (Fin 4) := [3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 2]

@[expose]
def r121 : List (Fin 4) := [1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 2, 3, 2, 1, 2]

@[expose]
def r122 : List (Fin 4) := [2, 2, 2, 1, 1, 0, 1, 2, 3, 2, 1, 2, 1, 1, 1]

@[expose]
def r123 : List (Fin 4) := [0, 1, 0, 1, 2, 3, 0, 0, 3, 3, 3, 3, 3]

@[expose]
def r124 : List (Fin 4) := [1, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1, 2, 2]

@[expose]
def r125 : List (Fin 4) := [2, 1, 1, 1, 1, 1, 2, 2, 1, 0, 3, 2, 3]

@[expose]
def r126 : List (Fin 4) := [1, 0, 1, 2, 3, 3, 0, 0, 0, 3, 3, 3, 2, 3, 0]

@[expose]
def r127 : List (Fin 4) := [1, 2, 3, 3, 0, 0, 0, 3, 3, 3, 2, 3, 0, 1, 0]

@[expose]
def r128 : List (Fin 4) := [3, 2, 3, 2, 1, 0, 1, 1, 1, 2, 2, 2, 1, 1, 0]

@[expose]
def r129 : List (Fin 4) := [0, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 3, 0, 3]

@[expose]
def r130 : List (Fin 4) := [3, 0, 3, 0, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3]

@[expose]
def r131 : List (Fin 4) := [1, 1, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 2, 1, 2]

@[expose]
def r132 : List (Fin 4) := [2, 1, 2, 1, 1, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2]

@[expose]
def r133 : List (Fin 4) := [2, 3, 0, 0, 1, 0, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1]

@[expose]
def r134 : List (Fin 4) := [3, 0, 0, 1, 0, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 2]

@[expose]
def r135 : List (Fin 4) := [1, 0, 3, 0, 1, 0, 3, 3, 0, 1, 0, 3, 2, 3, 2, 2]

@[expose]
def r136 : List (Fin 4) := [0, 3, 0, 1, 0, 3, 3, 0, 1, 0, 3, 2, 3, 2, 2, 1]

@[expose]
def r137 : List (Fin 4) := [1, 0, 3, 3, 0, 1, 0, 3, 2, 3, 2, 2, 1, 0, 3, 0]

@[expose]
def r138 : List (Fin 4) := [0, 0, 3, 0, 1, 0, 3, 3, 2, 3, 2, 1]

@[expose]
def r139 : List (Fin 4) := [0, 3, 0, 1, 0, 3, 3, 2, 3, 2, 1, 0]

@[expose]
def r140 : List (Fin 4) := [1, 0, 3, 3, 2, 3, 2, 1, 0, 0, 3, 0]

@[expose]
def r141 : List (Fin 4) := [3, 2, 3, 2, 1, 0, 0, 3, 0, 1, 0, 3]

@[expose]
def r142 : List (Fin 4) := [1, 0, 0, 3, 0, 1, 0, 3, 3, 2, 3, 2]

@[expose]
def r143 : List (Fin 4) := [3, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2, 2]

@[expose]
def r144 : List (Fin 4) := [1, 1, 2, 3, 2, 1, 2, 2, 3, 0, 1, 0]

@[expose]
def r145 : List (Fin 4) := [3, 2, 1, 2, 2, 3, 0, 1, 0, 1, 1, 2]

@[expose]
def r146 : List (Fin 4) := [2, 2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1]

@[expose]
def r147 : List (Fin 4) := [2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2]

@[expose]
def r148 : List (Fin 4) := [2, 3, 2, 2, 3, 2, 1, 0, 3, 0, 0, 1, 0, 1]

@[expose]
def r149 : List (Fin 4) := [1, 0, 3, 0, 0, 1, 0, 1, 2, 3, 2, 2, 3, 2]

@[expose]
def r150 : List (Fin 4) := [3, 0, 0, 1, 0, 1, 2, 3, 2, 2, 3, 2, 1, 0]

@[expose]
def r151 : List (Fin 4) := [1, 2, 3, 0, 1, 0, 0, 1, 0, 3, 2, 3, 2, 2]

@[expose]
def r152 : List (Fin 4) := [3, 0, 1, 0, 0, 1, 0, 3, 2, 3, 2, 2, 1, 2]

@[expose]
def r153 : List (Fin 4) := [0, 3, 2, 3, 2, 2, 1, 2, 3, 0, 1, 0, 0, 1]

@[expose]
def r154 : List (Fin 4) := [0, 3, 0, 1, 0, 0, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1]

@[expose]
def r155 : List (Fin 4) := [3, 0, 1, 1, 0, 3, 0, 1, 0, 3, 2, 2, 3, 2, 1, 2]

@[expose]
def r156 : List (Fin 4) := [2, 1, 0, 3, 0, 1, 2, 2, 1, 2, 3, 0, 3, 0, 0, 3]

@[expose]
def r157 : List (Fin 4) := [0, 1, 2, 2, 1, 2, 3, 0, 3, 0, 0, 3, 2, 1, 0, 3]

@[expose]
def r158 : List (Fin 4) := [2, 1, 2, 3, 0, 1, 2, 2, 1, 2, 1, 0, 3, 0, 0, 3]

@[expose]
def r159 : List (Fin 4) := [0, 1, 2, 2, 1, 2, 1, 0, 3, 0, 0, 3, 2, 1, 2, 3]

@[expose]
def r160 : List (Fin 4) := [2, 2, 2, 1, 2, 2, 1, 2, 3, 0, 1, 0, 0, 0, 0, 3]

@[expose]
def r161 : List (Fin 4) := [0, 1, 2, 2, 2, 2, 3, 2, 1, 0, 3, 0, 0, 3, 0, 0]

@[expose]
def r162 : List (Fin 4) := [0, 0, 0, 1, 2, 2, 1, 0, 3, 2, 3, 3]

@[expose]
def r163 : List (Fin 4) := [0, 0, 1, 2, 2, 1, 0, 3, 2, 3, 3, 0]

@[expose]
def r164 : List (Fin 4) := [0, 1, 2, 2, 1, 0, 3, 2, 3, 3, 0, 0]

@[expose]
def r165 : List (Fin 4) := [1, 2, 2, 1, 0, 3, 2, 3, 3, 0, 0, 0]

@[expose]
def r166 : List (Fin 4) := [0, 3, 2, 3, 3, 0, 0, 0, 1, 2, 2, 1]

@[expose]
def r167 : List (Fin 4) := [2, 3, 3, 0, 0, 0, 1, 2, 2, 1, 0, 3]

@[expose]
def r168 : List (Fin 4) := [3, 3, 0, 0, 0, 1, 2, 2, 1, 0, 3, 2]

@[expose]
def r169 : List (Fin 4) := [3, 0, 0, 0, 1, 2, 2, 1, 0, 3, 2, 3]

@[expose]
def r170 : List (Fin 4) := [1, 1, 0, 1, 2, 3, 0, 0, 3, 2, 2, 2]

@[expose]
def r171 : List (Fin 4) := [1, 0, 1, 2, 3, 0, 0, 3, 2, 2, 2, 1]

@[expose]
def r172 : List (Fin 4) := [0, 1, 2, 3, 0, 0, 3, 2, 2, 2, 1, 1]

@[expose]
def r173 : List (Fin 4) := [2, 3, 0, 0, 3, 2, 2, 2, 1, 1, 0, 1]

@[expose]
def r174 : List (Fin 4) := [3, 2, 2, 2, 1, 1, 0, 1, 2, 3, 0, 0]

@[expose]
def r175 : List (Fin 4) := [2, 2, 2, 1, 1, 0, 1, 2, 3, 0, 0, 3]

@[expose]
def r176 : List (Fin 4) := [2, 2, 1, 1, 0, 1, 2, 3, 0, 0, 3, 2]

@[expose]
def r177 : List (Fin 4) := [2, 1, 1, 0, 1, 2, 3, 0, 0, 3, 2, 2]

@[expose]
def r178 : List (Fin 4) := [1, 0, 3, 2, 3, 2, 1, 1, 0, 3, 0, 0, 0, 3, 2, 2]

@[expose]
def r179 : List (Fin 4) := [3, 2, 1, 1, 0, 3, 0, 0, 0, 3, 2, 2, 1, 0, 3, 2]

@[expose]
def r180 : List (Fin 4) := [3, 0, 1, 0, 1, 2, 3, 0, 0, 1, 2, 2, 2, 1, 2, 3]

@[expose]
def r181 : List (Fin 4) := [3, 0, 0, 1, 2, 2, 2, 1, 2, 3, 3, 0, 1, 0, 1, 2]

@[expose]
def r182 : List (Fin 4) := [2, 1, 0, 3, 2, 3, 2, 3, 0, 3, 0, 0, 0, 1, 1, 2]

@[expose]
def r183 : List (Fin 4) := [3, 0, 3, 0, 0, 0, 1, 1, 2, 2, 1, 0, 3, 2, 3, 2]

@[expose]
def r184 : List (Fin 4) := [1, 0, 1, 0, 1, 2, 3, 0, 0, 3, 3, 2, 2, 2, 1, 2]

@[expose]
def r185 : List (Fin 4) := [0, 0, 3, 3, 2, 2, 2, 1, 2, 1, 0, 1, 0, 1, 2, 3]

@[expose]
def r186 : List (Fin 4) := [1, 1, 1, 0, 3, 3, 3, 3, 0, 0, 3, 2, 3, 2, 1, 1]

@[expose]
def r187 : List (Fin 4) := [3, 3, 3, 0, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1, 0, 3]

@[expose]
def r188 : List (Fin 4) := [3, 0, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1, 0, 3, 3, 3]

@[expose]
def r189 : List (Fin 4) := [1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 0, 1, 0, 1, 2, 2]

@[expose]
def r190 : List (Fin 4) := [1, 1, 2, 3, 3, 3, 3, 3, 0, 1, 0, 1, 2, 2, 1, 1]

@[expose]
def r191 : List (Fin 4) := [3, 3, 3, 0, 1, 0, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3]

@[expose]
def r192 : List (Fin 4) := [3, 0, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 0, 0]

@[expose]
def r193 : List (Fin 4) := [1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 0, 0, 3, 0]

@[expose]
def r194 : List (Fin 4) := [2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 0, 0, 3, 0, 1]

@[expose]
def r195 : List (Fin 4) := [1, 0, 0, 3, 0, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2]

@[expose]
def r196 : List (Fin 4) := [3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 3, 2, 1, 2, 2]

@[expose]
def r197 : List (Fin 4) := [0, 3, 2, 1, 2, 2, 3, 0, 1, 0, 3, 3, 0, 3, 0]

@[expose]
def r198 : List (Fin 4) := [3, 2, 1, 2, 2, 3, 0, 1, 0, 3, 3, 0, 3, 0, 0]

@[expose]
def r199 : List (Fin 4) := [1, 2, 2, 3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 3, 2]

@[expose]
def r200 : List (Fin 4) := [0, 3, 3, 3, 3, 0, 0, 3, 2, 3, 3, 0, 0, 0, 1]

@[expose]
def r201 : List (Fin 4) := [3, 0, 0, 3, 2, 3, 3, 0, 0, 0, 1, 0, 3, 3, 3]

@[expose]
def r202 : List (Fin 4) := [3, 3, 0, 0, 0, 1, 0, 3, 3, 3, 3, 0, 0, 3, 2]

@[expose]
def r203 : List (Fin 4) := [3, 0, 0, 0, 1, 0, 3, 3, 3, 3, 0, 0, 3, 2, 3]

@[expose]
def r204 : List (Fin 4) := [1, 1, 0, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2]

@[expose]
def r205 : List (Fin 4) := [1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 0, 1, 2, 2]

@[expose]
def r206 : List (Fin 4) := [2, 3, 2, 2, 2, 1, 1, 0, 1, 2, 2, 1, 1, 1, 1]

@[expose]
def r207 : List (Fin 4) := [0, 3, 2, 1, 0, 3, 0, 1, 2, 1, 0, 3, 2, 3, 3, 0]

@[expose]
def r208 : List (Fin 4) := [1, 0, 3, 0, 1, 2, 1, 0, 3, 2, 3, 3, 0, 0, 3, 2]

@[expose]
def r209 : List (Fin 4) := [3, 3, 0, 0, 3, 2, 1, 0, 3, 0, 1, 2, 1, 0, 3, 2]

@[expose]
def r210 : List (Fin 4) := [3, 0, 1, 2, 2, 1, 1, 0, 1, 2, 3, 0, 3, 2, 1, 2]

@[expose]
def r211 : List (Fin 4) := [2, 2, 1, 1, 0, 1, 2, 3, 0, 3, 2, 1, 2, 3, 0, 1]

@[expose]
def r212 : List (Fin 4) := [1, 0, 3, 2, 3, 0, 3, 3, 3, 3, 3, 0, 1, 0, 0]

@[expose]
def r213 : List (Fin 4) := [2, 3, 0, 3, 3, 3, 3, 3, 0, 1, 0, 0, 1, 0, 3]

@[expose]
def r214 : List (Fin 4) := [3, 3, 3, 3, 0, 1, 0, 0, 1, 0, 3, 2, 3, 0, 3]

@[expose]
def r215 : List (Fin 4) := [3, 0, 1, 0, 0, 1, 0, 3, 2, 3, 0, 3, 3, 3, 3]

@[expose]
def r216 : List (Fin 4) := [0, 1, 0, 0, 1, 0, 3, 2, 3, 0, 3, 3, 3, 3, 3]

@[expose]
def r217 : List (Fin 4) := [1, 1, 1, 1, 1, 2, 1, 0, 1, 2, 3, 2, 2, 3, 2]

@[expose]
def r218 : List (Fin 4) := [1, 1, 2, 1, 0, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1]

@[expose]
def r219 : List (Fin 4) := [0, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 1, 1, 2, 1]

@[expose]
def r220 : List (Fin 4) := [0, 0, 0, 1, 2, 1, 0, 1, 2, 3, 2, 2, 3, 3]

@[expose]
def r221 : List (Fin 4) := [1, 0, 1, 2, 3, 2, 2, 3, 3, 0, 0, 0, 1, 2]

@[expose]
def r222 : List (Fin 4) := [2, 3, 2, 2, 3, 3, 0, 0, 0, 1, 2, 1, 0, 1]

@[expose]
def r223 : List (Fin 4) := [3, 2, 2, 3, 3, 0, 0, 0, 1, 2, 1, 0, 1, 2]

@[expose]
def r224 : List (Fin 4) := [2, 3, 3, 0, 0, 0, 1, 2, 1, 0, 1, 2, 3, 2]

@[expose]
def r225 : List (Fin 4) := [3, 3, 0, 0, 0, 1, 2, 1, 0, 1, 2, 3, 2, 2]

@[expose]
def r226 : List (Fin 4) := [1, 0, 0, 1, 0, 3, 2, 3, 0, 3, 2, 2, 2, 1]

@[expose]
def r227 : List (Fin 4) := [0, 0, 1, 0, 3, 2, 3, 0, 3, 2, 2, 2, 1, 1]

@[expose]
def r228 : List (Fin 4) := [1, 0, 3, 2, 3, 0, 3, 2, 2, 2, 1, 1, 0, 0]

@[expose]
def r229 : List (Fin 4) := [0, 3, 2, 3, 0, 3, 2, 2, 2, 1, 1, 0, 0, 1]

@[expose]
def r230 : List (Fin 4) := [3, 0, 3, 2, 2, 2, 1, 1, 0, 0, 1, 0, 3, 2]

@[expose]
def r231 : List (Fin 4) := [2, 2, 2, 1, 1, 0, 0, 1, 0, 3, 2, 3, 0, 3]

@[expose]
def r232 : List (Fin 4) := [2, 1, 1, 0, 0, 1, 0, 3, 2, 3, 0, 3, 2, 2]

@[expose]
def r233 : List (Fin 4) := [0, 0, 3, 3, 0, 1, 2, 3, 0, 0, 3, 2, 2, 3, 0]

@[expose]
def r234 : List (Fin 4) := [0, 3, 3, 0, 1, 2, 3, 0, 0, 3, 2, 2, 3, 0, 0]

@[expose]
def r235 : List (Fin 4) := [3, 3, 0, 1, 2, 3, 0, 0, 3, 2, 2, 3, 0, 0, 0]

@[expose]
def r236 : List (Fin 4) := [0, 1, 2, 3, 0, 0, 3, 2, 2, 3, 0, 0, 0, 3, 3]

@[expose]
def r237 : List (Fin 4) := [0, 0, 3, 2, 2, 3, 0, 0, 0, 3, 3, 0, 1, 2, 3]

@[expose]
def r238 : List (Fin 4) := [2, 2, 3, 0, 0, 0, 3, 3, 0, 1, 2, 3, 0, 0, 3]

@[expose]
def r239 : List (Fin 4) := [2, 3, 0, 0, 0, 3, 3, 0, 1, 2, 3, 0, 0, 3, 2]

@[expose]
def r240 : List (Fin 4) := [0, 0, 1, 2, 2, 1, 0, 3, 2, 1, 1, 2, 2, 2, 1]

@[expose]
def r241 : List (Fin 4) := [1, 2, 2, 1, 0, 3, 2, 1, 1, 2, 2, 2, 1, 0, 0]

@[expose]
def r242 : List (Fin 4) := [2, 1, 0, 3, 2, 1, 1, 2, 2, 2, 1, 0, 0, 1, 2]

@[expose]
def r243 : List (Fin 4) := [1, 0, 3, 2, 1, 1, 2, 2, 2, 1, 0, 0, 1, 2, 2]

@[expose]
def r244 : List (Fin 4) := [3, 2, 1, 1, 2, 2, 2, 1, 0, 0, 1, 2, 2, 1, 0]

@[expose]
def r245 : List (Fin 4) := [1, 1, 2, 2, 2, 1, 0, 0, 1, 2, 2, 1, 0, 3, 2]

@[expose]
def r246 : List (Fin 4) := [2, 2, 2, 1, 0, 0, 1, 2, 2, 1, 0, 3, 2, 1, 1]

@[expose]
def r247 : List (Fin 4) := [2, 2, 1, 0, 0, 1, 2, 2, 1, 0, 3, 2, 1, 1, 2]

@[expose]
def r248 : List (Fin 4) := [0, 0, 3, 3, 3, 3, 2, 3, 0, 1, 0, 1, 1, 2, 3]

@[expose]
def r249 : List (Fin 4) := [0, 3, 3, 3, 3, 2, 3, 0, 1, 0, 1, 1, 2, 3, 0]

@[expose]
def r250 : List (Fin 4) := [3, 3, 2, 3, 0, 1, 0, 1, 1, 2, 3, 0, 0, 3, 3]

@[expose]
def r251 : List (Fin 4) := [1, 0, 1, 1, 2, 3, 0, 0, 3, 3, 3, 3, 2, 3, 0]

@[expose]
def r252 : List (Fin 4) := [1, 1, 2, 3, 0, 0, 3, 3, 3, 3, 2, 3, 0, 1, 0]

@[expose]
def r253 : List (Fin 4) := [1, 2, 3, 0, 0, 3, 3, 3, 3, 2, 3, 0, 1, 0, 1]

@[expose]
def r254 : List (Fin 4) := [0, 3, 3, 2, 3, 2, 1, 0, 1, 1, 1, 1, 2, 2, 1]

@[expose]
def r255 : List (Fin 4) := [3, 3, 2, 3, 2, 1, 0, 1, 1, 1, 1, 2, 2, 1, 0]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
