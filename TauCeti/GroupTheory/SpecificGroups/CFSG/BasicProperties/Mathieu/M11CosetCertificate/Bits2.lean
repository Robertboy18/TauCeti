/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableBits

/-!
# M11 coset certificate: Bits2

Literal checkpoints: four natural-number masks at each stage.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def bits032row0 : ℕ :=
  0x39ff9ee6dafd9fffffdf5ffffe3fbfffffe99bfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa2350d659aa50a8aa287d3f62d1da5afd6ee8ef5775af392fdf9f757fe7f * 2 ^ 240 +
  0x20d42202230432da22271c04b208a254d6835c205564abafa8b4daa395bc * 2 ^ 480 +
  0x1080141894202302b90300481282840c802240a40a2212c49815a2534da1 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits032row1 : ℕ :=
  0xf24f72fadf64bfbffdffff7f5bf7cf7fddf7ff2d7ffffefff9fb7ffffff7 * 2 ^ 0 +
  0x905e2cb8901b55383d91dd2e3cd82958eddb08faae1a65b5c986a7e47fef * 2 ^ 240 +
  0x010151409e692105a689015a4c0414911d199b8538488858fc67d5310984 * 2 ^ 480 +
  0x892068e44012c4a00a001992294818a04d0573495c88c88010a885041048 * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits032row2 : ℕ :=
  0x9f03fbfd7b6eeffc4b5ef7dfffcbfffff7fdf7ff79efbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353107757cb98abf374cdcfe78b6f7b143577b0edbe6a47fbf35dc0f6 * 2 ^ 240 +
  0x86488419859042660940a08908b5590aa80f26598e3097ad2f22c2470849 * 2 ^ 480 +
  0x264d92008181101544d4240c8215210129488000a0150998a16111202282 * 2 ^ 720 +
  0x11084860 * 2 ^ 960

@[expose]
def bits032row3 : ℕ :=
  0xeffaed85b63f9657ffe6beeb9f9fbb9f7ffffbcffefefefff5f7fffbfffe * 2 ^ 0 +
  0x2b4684f6adff7df75d6c5bed928edc523ce57ffb2fd78efd6b37cad5d7dc * 2 ^ 240 +
  0x583208bd48328c9850145325115e1220036882f749a35404015df8196b32 * 2 ^ 480 +
  0x401201032a4c08480228c2254420425612900c130142242346424d88e814 * 2 ^ 720 +
  0x8910601 * 2 ^ 960

@[expose]
def bits032 : Vector ℕ 4 := #v[bits032row0, bits032row1, bits032row2, bits032row3]

@[expose]
def bits033row0 : ℕ :=
  0x39ff9ee6dafd9fffffdf5ffffe3fbfffffe99bfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa2350d659aa50a8aa287d3f62d1da5afd6ee8ef5775af392fdf9f757fe7f * 2 ^ 240 +
  0x20d42202230432da22271c04b208a254d6835c205564abafa8b4daa395bc * 2 ^ 480 +
  0x1080141894202302b90300481282840c802240a40a2212c49815a2534da1 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits033row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffcf7fddf7ff2f7ffffefff9fb7ffffff7 * 2 ^ 0 +
  0x905eacb8901b55b83d91dd2e3cde2958edff08faae1a65b7c986a7e47fef * 2 ^ 240 +
  0x010151429e692105a689015a5c0414911d199b8538c88858fc67d531098c * 2 ^ 480 +
  0x892068e44012c4a20a009992294818a04d0573495c88c88010aac5041048 * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits033row2 : ℕ :=
  0x9f03fbfd7b6feffc4b5ef7dfffcffffff7fdf7ff7befbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353107757cb99abf374cdcfe78b6f7b143777b0edbe6a4ffbf35dc0f6 * 2 ^ 240 +
  0x86488419859042660940a08908f5590aa80f26598e3097ad2f22c2470849 * 2 ^ 480 +
  0x264d92008181101544d4240c8215210129c88000a0150998a16111202282 * 2 ^ 720 +
  0x11084860 * 2 ^ 960

@[expose]
def bits033row3 : ℕ :=
  0xeffaed85b63f9657ffe6beeb9f9fbb9f7ffffbcffefefefff5f7fffbfffe * 2 ^ 0 +
  0x2f4684f6adff7df75d6c5bed928edc523ce57ffb2fd78efd6b37cad5d7dc * 2 ^ 240 +
  0x583288bd48328c9850145325115e1220036882f749a35404015df81d6b32 * 2 ^ 480 +
  0x401201032a4c084c0228c2254420425612900c130142242346424d88e814 * 2 ^ 720 +
  0x8910601 * 2 ^ 960

@[expose]
def bits033 : Vector ℕ 4 := #v[bits033row0, bits033row1, bits033row2, bits033row3]

@[expose]
def bits034row0 : ℕ :=
  0x39ff9ee6defd9fffffdf5ffffe3fbfffffe99bfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa2350d659aa50a8aa287d3f62d1da5afd6ef8ef5775af392fdf9f757fe7f * 2 ^ 240 +
  0x20d4220a230432da22271c04b208a254d6835c205564abafa8b4daa395bc * 2 ^ 480 +
  0x1080141894202302b90300481282840c802240a40a2212c49815a2534da1 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits034row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffcf7fddf7ff3f7ffffefff9fb7ffffff7 * 2 ^ 0 +
  0x905eacb8901b5db83d91dd2e3cde29d8edff08faae1a65b7c9c6a7e47fef * 2 ^ 240 +
  0x010151429f692105a689015a5c0414911f199b8538c88859fc67d531098c * 2 ^ 480 +
  0x892068e44012c4a20a009992294818a04d0573495c88c88010aac5041048 * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits034row2 : ℕ :=
  0x9f03fbfd7b6feffd4b5ef7dfffdffffff7fdf7ff7befbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353507757cb9dabf374cdcfe78b6f7b143777b0edbe6a6ffbf35dc0f6 * 2 ^ 240 +
  0xa648841d859242660940a08908f5590aa84f26598e32d7ad2fa2c2470859 * 2 ^ 480 +
  0x264d92008181101544d4240c8235610129c88000a0150998a16111202282 * 2 ^ 720 +
  0x110a4860 * 2 ^ 960

@[expose]
def bits034row3 : ℕ :=
  0xeffaed85b63f9657ffe6beeb9f9fbf9f7ffffbcffefffefff5f7fffbfffe * 2 ^ 0 +
  0x2f4684f6adff7df75d6c5bed928edc523ce57ffb2fd78efd6b37cad5d7dc * 2 ^ 240 +
  0x583288bd48328c9851145325115e1220036882f749a35406015df81d6b32 * 2 ^ 480 +
  0x401201032a4c084c0238c2254420425612900c13014224a346424d88e814 * 2 ^ 720 +
  0x8910601 * 2 ^ 960

@[expose]
def bits034 : Vector ℕ 4 := #v[bits034row0, bits034row1, bits034row2, bits034row3]

@[expose]
def bits035row0 : ℕ :=
  0x39ffbfe6defd9fffffdf5ffffe3fbfffffe9dbfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa2350d659aa50a8ab287d3f62d1da5aff6ff8ef5775af392fdf9f757ff7f * 2 ^ 240 +
  0x20d4220a230432da22271c04b208a254d6835c205564abafa8b4daa3b5bc * 2 ^ 480 +
  0x9080141894202302b91700481282840c802240a40a2212c49815a2534da1 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits035row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffef7fddf7ff3f7ffffefff9fb7ffffff7 * 2 ^ 0 +
  0x905eacb8901bddb83d91dd2e3cdea9d8edff08fabe1a65b7c9e6a7e47fef * 2 ^ 240 +
  0x010151429f692105a689015a5c041c911f199b8538c88859fc67d531098c * 2 ^ 480 +
  0x8920e8e44012c4a20a409992294818a04d0573495c88c8c010aac5041048 * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits035row2 : ℕ :=
  0x9f03fbfd7b6feffd5b5ef7dfffdffffff7fdf7ff7befbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353707757cb9dabf374cdcfe78b6f7b143777b0edbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa648841d8592c2660940a08908f5590aa84f26598e32d7ad2fa2c2470859 * 2 ^ 480 +
  0x264d92008181101544d4240c823561012bc88000a0150998a16111202282 * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits035row3 : ℕ :=
  0xeffaed85b63f9657ffe6beefbf9fbf9f7ffffbcffefffefff5f7fffbfffe * 2 ^ 0 +
  0x2f4684f6adff7df75d6c5bedd28edc523ce57ffb2fd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd48328c9851145325115e12200368c2f749a35406015df81d6b32 * 2 ^ 480 +
  0x401201032a4c084c0238c2254420425612900c13014224e346424d88e814 * 2 ^ 720 +
  0x8910601 * 2 ^ 960

@[expose]
def bits035 : Vector ℕ 4 := #v[bits035row0, bits035row1, bits035row2, bits035row3]

@[expose]
def bits036row0 : ℕ :=
  0x39ffbfe6defd9fffffdf5ffffe3fbfffffe9dbfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa23d0d659aa50a9ab287d3f62d1da5aff6ff8ef5775af392fdf9f757ff7f * 2 ^ 240 +
  0x20d4220a231432da22271c04b208a254d6835c205564abafa8b6daa3b5be * 2 ^ 480 +
  0x9081141894202302b91700481282840c802240a40e2212c69815a2534da1 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits036row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffef7fddf7ff3f7ffffefff9fb7ffffff7 * 2 ^ 0 +
  0x905eacb8901bddb83d91dd2e3edea9d8edff08fabe1a65b7c9e6a7e47fef * 2 ^ 240 +
  0x010151429f692107a689015a5c043c911f199b8d38c88859fc67d531098c * 2 ^ 480 +
  0x8920e8e44032c4a20e409992294818a04d0573495d88c8c010aac5241048 * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits036row2 : ℕ :=
  0x9f03fbfd7b6feffd5b5ef7dfffdffffff7fdf7ff7befbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353707757eb9dabf374cdcfe7cb6f7b143777b0edbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa648841d8592c2660943a08908f5590aa84f26598e32d7ad2fa2c2470859 * 2 ^ 480 +
  0x264d920081b1101544d4240c823561012bc88000a0150998a16111202292 * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits036row3 : ℕ :=
  0xeffaed85b63f9757ffe6beefbf9fbf9f7ffffbcffefffefff5f7fffbfffe * 2 ^ 0 +
  0x2f4686f6adff7df75d6c5bedd28edc523ce57fff2fd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd48328c9851155325935e12200368c2f749e35406015df81d6b32 * 2 ^ 480 +
  0x401205032a4c084c0238c2254420425612900c13014264e346424d88e814 * 2 ^ 720 +
  0x8910601 * 2 ^ 960

@[expose]
def bits036 : Vector ℕ 4 := #v[bits036row0, bits036row1, bits036row2, bits036row3]

@[expose]
def bits037row0 : ℕ :=
  0x39ffbfe6defd9fffffdf5ffffe3fbfffffe9dbfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa23d0d659aa50abab287d3f62d5da5aff6ff8ef5775af392fdf9f757ff7f * 2 ^ 240 +
  0x20d4222a231432da22271c54b20ca255d6835c205564abafa8b6faa3b5be * 2 ^ 480 +
  0x90a1141894202302b91700485282840c802340a40e2212c69815a2534da1 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits037row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffef7fddf7ff3f7ffffefff9fb7ffffff7 * 2 ^ 0 +
  0x905eacb8901bddb83d91dd2e3edea9d8edff08fabe1a65b7c9e6a7e47fef * 2 ^ 240 +
  0x010151429f692107a689015a5c043c911f1b9b8d38c88859fc67d531098c * 2 ^ 480 +
  0x89a0e8e44032c4a28e409992294918a04d0773495d88c8c010aac5241048 * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits037row2 : ℕ :=
  0x9f03fbfd7f6feffd5b5ef7dfffdffffff7fdf7ff7befbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353707757eb9dabf374cdcfe7cb6f7b153777b0edbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa648841d8592ca660943a08908f5590aa84f66598e32d7ad2fa2c6470859 * 2 ^ 480 +
  0x364d920089b1301544d4260c823561012bc88000a0158998a16115202292 * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits037row3 : ℕ :=
  0xeffaed85b63f9757ffe6beefbf9fbf9f7ffffbcffefffefff5f7fffbfffe * 2 ^ 0 +
  0x2f4686f6adff7df75d6c5bedd28edc523ce57fff2fd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd4c328c9851155325935e12200378c2f749e3d406015df81d6b32 * 2 ^ 480 +
  0x401205032a5c084c0238c2254420425612900c13054264e346424d88e814 * 2 ^ 720 +
  0x8910601 * 2 ^ 960

@[expose]
def bits037 : Vector ℕ 4 := #v[bits037row0, bits037row1, bits037row2, bits037row3]

@[expose]
def bits038row0 : ℕ :=
  0x39ffbfe6defd9fffffdf5ffffe3fbfffffe9dbfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa23d8d659aa50abab287d3f62d5da5aff6ff9ef5775af392fdf9f757ff7f * 2 ^ 240 +
  0x20d4222a231432da22271c54f20ca255d6835c205564abafa8b6faa3b5be * 2 ^ 480 +
  0x90a1141894203302b91700485282840c802340a40e2212c69815a2534df1 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits038row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffef7fddf7ff3f7ffffefff9fb7ffffff7 * 2 ^ 0 +
  0x915eacb8901bddb83d91dd2e3edea9d8edff08fabe1a65b7c9e6a7e47fef * 2 ^ 240 +
  0x210151429f692107a689015a5c043c911f1b9b8d38c88859fc6fd531098c * 2 ^ 480 +
  0x89a0e9e44032e4a28e409b922b4b18a04d0773495d88c8c010aac5a41048 * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits038row2 : ℕ :=
  0x9f03fbfd7f6feffd5b5ef7dfffdffffff7fdf7ff7befbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353707f5feb9dabf774cdcfe7cb6f7b153777b0edbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa64a841d9592ca660943a48918f5594aa84f66598e32d7ad2fa2c6470859 * 2 ^ 480 +
  0x364d920089b1301544d4260c823561012bc88000a0158998a16115202292 * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits038row3 : ℕ :=
  0xeffaed85b63f9757ffe6beefbf9fbf9f7ffffbcffefffefff5f7fffbfffe * 2 ^ 0 +
  0x2f4686f6adff7df75d6c5bedd28edc523ee57fff2fd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd4c328c9851155b25935e12200378c2f749e3d406015ff81d6b32 * 2 ^ 480 +
  0x40122503aa5c084c0238c2254460425612900e13054264e346424d88e814 * 2 ^ 720 +
  0x8912603 * 2 ^ 960

@[expose]
def bits038 : Vector ℕ 4 := #v[bits038row0, bits038row1, bits038row2, bits038row3]

@[expose]
def bits039row0 : ℕ :=
  0x39ffbfe6defd9fffffdf5ffffe3fbfffffe9dbfefdfdef7efffeff7fbfff * 2 ^ 0 +
  0xa23d8d659aa50abab287d3f62d5da5aff6ff9ef5775af392fdf9f757ff7f * 2 ^ 240 +
  0x20d4222a231432da22271c54f20ca655f6835c205564abafa8b6faa3b5be * 2 ^ 480 +
  0x90e1141894203302b9170048528a840c802340b60e221ac69815a2534df9 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits039row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffef7fddf7ff3f7ffffefff9fb7fffffff * 2 ^ 0 +
  0x915eacb8901bddb83d91dd2e3edeadd8edff08fabe9a65b7c9e6a7e47fef * 2 ^ 240 +
  0x210151429f692107a689095a5c443c911f1b9b8d38c88859fc6fd531198c * 2 ^ 480 +
  0x89a0e9e44032e4a28e609b922b4b18a04d0773495d88c8c010aac5a5104a * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits039row2 : ℕ :=
  0x9f03fbfd7f6feffd5b5ef7dfffdffffff7fdf7ff7befbf7bbffffdffffff * 2 ^ 0 +
  0xc4b353707f5feb9dabf774cdcfe7cb6f7b153777b0edbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa64a861d9592ca660b43a4c918f5594aa84f66598e32d7ad2fa2ce470859 * 2 ^ 480 +
  0x364d920089b1301544d42e8c823561012bc88000a2158998a16115202292 * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits039row3 : ℕ :=
  0xeffaed85b63f9757ffe6beefbf9fbf9f7ffffbcffefffefff5f7fffbfffe * 2 ^ 0 +
  0x2f4687f6adff7df75d6c5bedd28edc523fe57fffafd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd4c328c9871155b25935e12200378c2f749e3d406015ff81d6b36 * 2 ^ 480 +
  0x40122503ea5c084c0238c2254460435712900e13054264e346424d88e814 * 2 ^ 720 +
  0x8912603 * 2 ^ 960

@[expose]
def bits039 : Vector ℕ 4 := #v[bits039row0, bits039row1, bits039row2, bits039row3]

@[expose]
def bits040row0 : ℕ :=
  0x39ffbfe6defd9fffffdf5ffffe3fbfffffedfbfefdfdeffefffeff7fffff * 2 ^ 0 +
  0xa23d8d659aa50abab287d3f62d5da5aff6ff9ef5775afb92fdf9f757ff7f * 2 ^ 240 +
  0x20d4222a231432da22271c54f21ca655f6835c205564abafa8b6faa3b5be * 2 ^ 480 +
  0x90e1141894203302b9170048528a840c802340b60e221ac69815a2534df9 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits040row1 : ℕ :=
  0xf25f72faff74bfbffdffff7f5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0x915eacb8901bddb83d91dd2e3edeadd8edff0afabe9a65bfc9e6a7e47fef * 2 ^ 240 +
  0x210153429f692187a689095a5c443c911f1b9b8d38c88859fc6fd531198c * 2 ^ 480 +
  0x89a0e9e44032e4a28e609b922b4b18a04d0773495d88c8c010aac5a5104a * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits040row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7dfffdffffff7fdf7ffffefbf7bffffffffffff * 2 ^ 0 +
  0xc4b353707f5feb9dabf774ddcfe7cb6f7b153777b0edbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa64a869d9592ca660b43a4c918f5594aa84f66598e32d7ad2fa2cf670859 * 2 ^ 480 +
  0x364d920089b1301544d42eac823561012bc88000a2158998a1611520229a * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits040row3 : ℕ :=
  0xeffaed8db63fd757ffe6beefbf9fbf9f7ffffbcffefffefff5fffffbffff * 2 ^ 0 +
  0x2f4687f6adff7df75d6c5bedd28edc523fe57fffafd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd4c328c9871155b25935f12200378c2f749e3d406015ff81d6b36 * 2 ^ 480 +
  0x40122503ea5c084c0238c2254460435712900e13054264e346424d88e81c * 2 ^ 720 +
  0x8912603 * 2 ^ 960

@[expose]
def bits040 : Vector ℕ 4 := #v[bits040row0, bits040row1, bits040row2, bits040row3]

@[expose]
def bits041row0 : ℕ :=
  0x39ffffe6defd9fffffdf5fffff3fbfffffeffffffdfdeffefffeffffffff * 2 ^ 0 +
  0xa23d8d659aad0abab287d3f62d5da5aff6ff9ef5775afbb2fdf9f757ffff * 2 ^ 240 +
  0x20d4222a231432da22271c54f21ca655f6835c205564abafa8b6faa3b5be * 2 ^ 480 +
  0x90e1141894203302b9170048528a840c802340b60e221ac69815a2534df9 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits041row1 : ℕ :=
  0xf25f72fbff74bfbffdffff7f5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0x915eacb8901bddfa3d91dd2e3edeedd8edff0afabe9a65bfd9e6a7e47fef * 2 ^ 240 +
  0x210153429f692187a689095a5c443c911f1b9b8d38c88859fc6fd531198c * 2 ^ 480 +
  0x89a0e9e44032e4a28e609b922b4b18a04d07734b5d88c8c010aac5a5104a * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits041row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7dffffffffffffdf7ffffefbf7bffffffffffff * 2 ^ 0 +
  0xc4b353787f5feb9dabf774ddcfe7cb6f7b153777b4fdbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa64a869d9592ca660b43a4c918f5594aa84f66598e32d7ad2fa2cf670859 * 2 ^ 480 +
  0x364d920089b1301544d42eac823561012bc88000a2158998a1611520229a * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits041row3 : ℕ :=
  0xeffaed8db63ff75ffff6beffbf9fff9f7ffffbdffefffefff5fffffbffff * 2 ^ 0 +
  0x2f468ff6adff7df75d6c5bedd28edc723fe57fffbfd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd4c328c9c71155b25935f12200378c2f749e3d406015ff81d6b36 * 2 ^ 480 +
  0x40122503ea5c084c0238c22544e0435712900e13054a64e346424d88e81c * 2 ^ 720 +
  0x8912603 * 2 ^ 960

@[expose]
def bits041 : Vector ℕ 4 := #v[bits041row0, bits041row1, bits041row2, bits041row3]

@[expose]
def bits042row0 : ℕ :=
  0x39ffffeedefd9fffffdf5fffff3fbfffffeffffffdfdeffefffeffffffff * 2 ^ 0 +
  0xa23d8d659aad0abab287d3f62d5da5aff6fffef7775afbb2fdf9f757ffff * 2 ^ 240 +
  0x20d4222a23d432da22271c54f21ca655f6835c285564abafa9b6faa3b5be * 2 ^ 480 +
  0x90e11418d4203302b9170048528a840c802340b60e221ac69815a2734df9 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits042row1 : ℕ :=
  0xf27f72fbff74bfbffdffff7f5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0xd15eacb8901bddfa3d91dd2e3edeedd8edff2afabe9e65bfd9e6a7e47fef * 2 ^ 240 +
  0x210153439f696197a689095a5c443c911f1b9b8d38c88859fd6fd531198c * 2 ^ 480 +
  0x89a0e9e44032e4a28e609b922b4b18a04d07734b5d88c8c010aac5a5104a * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits042row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7dffffffffffffdf7ffffefbffbffffffffffff * 2 ^ 0 +
  0xe4b353787f5feb9dabf774ddcfe7cb6f7b1d3777b4fdbe6a6ffbf35dc0f7 * 2 ^ 240 +
  0xa64a869f9592ca660b53a4c918f5595aa84f66598e32d7ad2fa2cf670859 * 2 ^ 480 +
  0x364d920089b1301544d42eac8235e1012bc88000a2158998a1611520229a * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits042row3 : ℕ :=
  0xeffaed8db63ff75ffff6beffff9fff9f7ffffbdffefffefff5fffffbffff * 2 ^ 0 +
  0x2f468ff6adff7df75d6c5bedd28fdc723fe77fffbfd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd4c328c9c71955b25935f12300378c2f749e3d406015ff81d6b36 * 2 ^ 480 +
  0x40522503ea5c084c0238c22544e0435712900e1b054a64e346424d88e81c * 2 ^ 720 +
  0x8912603 * 2 ^ 960

@[expose]
def bits042 : Vector ℕ 4 := #v[bits042row0, bits042row1, bits042row2, bits042row3]

@[expose]
def bits043row0 : ℕ :=
  0x3bffffeedefd9fffffdf5fffff3fbfffffeffffffdfdfffeffffffffffff * 2 ^ 0 +
  0xa23d8d659aad0abab287d3f62d5da5bff6fffef7775afbb2fdf9f757ffff * 2 ^ 240 +
  0x20d4222a23d473da22271c54f31ca655f6835c285564abefa9b6faa3b5be * 2 ^ 480 +
  0x90e11418d4203302b9170048528a840c802340b60e221ac69815a2734df9 * 2 ^ 720 +
  0x22469004 * 2 ^ 960

@[expose]
def bits043row1 : ℕ :=
  0xfa7ff2fbff74bfbffdffff7f5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0xd15eacb8901bddfa3d91ddae3edfedd8edff2afabe9e65bfd9e6a7e67fef * 2 ^ 240 +
  0x210353439f696197a689095a5c443c913f1b9b8d38c8c859fd6fd531198d * 2 ^ 480 +
  0x89a0e9e44032e4a28e609b922b4b18a04d07734b5d88c8c010aac5a5104a * 2 ^ 720 +
  0x420219a * 2 ^ 960

@[expose]
def bits043row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7dffffffffffffdffffffefbfffffffffffffff * 2 ^ 0 +
  0xe4b353787f5feb9dabf774ddcfe7cb6f7b1d3777b4fdbe6a6ffbf35dc8f7 * 2 ^ 240 +
  0xa66b86df9592ce660b53a4c918f5595aa84f66598e32d7ad2fa2cf670859 * 2 ^ 480 +
  0x364d920089b1301544d42eac8235e1012bc88400a2158998a1611520229a * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits043row3 : ℕ :=
  0xeffaed8dbe3ff75ffff6beffff9fff9f7ffffbdffefffefff5fffffbffff * 2 ^ 0 +
  0xaf46aff6adff7df75d6c5bedd28fdc723fe7ffffbfd78efd6b37cad5d7dd * 2 ^ 240 +
  0x583288bd6c328c9c71955b25935f52300378c2f749e3d406815ff81d6b36 * 2 ^ 480 +
  0x40522503ea5c084c0238c22544e0435712900e1b054a64e346424d88e81c * 2 ^ 720 +
  0x8912603 * 2 ^ 960

@[expose]
def bits043 : Vector ℕ 4 := #v[bits043row0, bits043row1, bits043row2, bits043row3]

@[expose]
def bits044row0 : ℕ :=
  0x3bffffeedefd9fffffdf5fffff3fbfffffeffffffdfdfffeffffffffffff * 2 ^ 0 +
  0xa23d8d659aad0abab2a7d3f62d5da5bff6fffef7f75afbb2fdf9f757ffff * 2 ^ 240 +
  0x20d4222a23d673da22271c74f35ca655f6835c2a5564abefa9b7faa3b5be * 2 ^ 480 +
  0x90e11418d4203302b9170048528a842c802340b60e221ac69817a2734df9 * 2 ^ 720 +
  0x22469014 * 2 ^ 960

@[expose]
def bits044row1 : ℕ :=
  0xfa7ff2fbff74bfbffdffff7f5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0xd15eacb8901bddfa3d91ddae3edfedd8edff2afabe9e65bfd9e6a7e67fef * 2 ^ 240 +
  0x310353439f696197a689095a5c443c913f1b9b8d3ac8c8d9fd6fd531198d * 2 ^ 480 +
  0x89a0e9e44032e4a28e609b922b4b18a44d07735b5d88c8c010abc5a5104a * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits044row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7dffffffffffffdffffffefbfffffffffffffff * 2 ^ 0 +
  0xf4b353787f5feb9dabf774ddcfe7cb6f7b1d3777b4fdbeea6ffbf35dc8f7 * 2 ^ 240 +
  0xb66b86df9592ce660b73a4c918f55b5aa84f66598e32d7ad2fa2cf672859 * 2 ^ 480 +
  0x374d920089b1301544d42eac8235e1012bc88400a2158998a16315202a9a * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits044row3 : ℕ :=
  0xeffaed8dbe3ff75ffff6beffff9fff9f7ffffbdffefffefff5fffffbffff * 2 ^ 0 +
  0xaf46aff6adff7df75d6c7bedd28fdc723fe7ffffbfd78efd6b37cad5d7dd * 2 ^ 240 +
  0x58328abd6c328c9c71955b25935f52300378c2f749e3d406815ff81d6b36 * 2 ^ 480 +
  0x40522503ea5c084c02b8c22544e0435712900e1b054a64f346424d88ec1c * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits044 : Vector ℕ 4 := #v[bits044row0, bits044row1, bits044row2, bits044row3]

@[expose]
def bits045row0 : ℕ :=
  0x3bffffeedefd9fffffdfdfffff3fbfffffeffffffdfdfffeffffffffffff * 2 ^ 0 +
  0xa23f8d659aad0abab2a7d3f62d5da5bff6fffef7f75afbb2fdf9ff57ffff * 2 ^ 240 +
  0x20d4222a63d673da22271c74f35ca655f6835c2a5566abefa9b7faa3b5be * 2 ^ 480 +
  0x90e11418d4203302b9170048528a842c802340b60e221ac69817a2734df9 * 2 ^ 720 +
  0x22469014 * 2 ^ 960

@[expose]
def bits045row1 : ℕ :=
  0xfa7ff2fbff74bfbffdffff7f5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0xd95eacb8901bddfa3d91ddae3edfedd8edff2afabe9e65bfd9e6a7e67fef * 2 ^ 240 +
  0x310353439f696597a689095b5d443e913f9b9b8d3ac8c8d9fd6fd531198d * 2 ^ 480 +
  0x89a0e9e44032e4a28e609b922b4b18b44d07735b5d88c8c010abc5a510da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits045row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7dffffffffffffdffffffefbfffffffffffffff * 2 ^ 0 +
  0xf4b353787f5feb9dabf774ddcfe7cb6f7b1f3777b4fdbeea6ffbf35dc8f7 * 2 ^ 240 +
  0xb66b86dfd5d2ce660b73acc918f55b5aa8cf66598e32d7ad2fa2cf672859 * 2 ^ 480 +
  0x374d920089b1301544d42eaca235e1012bc88400a2158998a16315202a9a * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits045row3 : ℕ :=
  0xeffaed8dbe3ff75ffff6beffff9fffbf7ffffbdffefffefff5fffffbffff * 2 ^ 0 +
  0xaf46aff6adff7df75d6c7bedd28fde723fe7ffffbfdfceff6b37cad5d7dd * 2 ^ 240 +
  0x58328abd6c328e9c71955b25935f56300378c2f749e3d406815ff81d6b36 * 2 ^ 480 +
  0x42522503ea5c284c02b8c22544e0435712900e1b854a64f746524d88ec1c * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits045 : Vector ℕ 4 := #v[bits045row0, bits045row1, bits045row2, bits045row3]

@[expose]
def bits046row0 : ℕ :=
  0x3bffffeedefd9fffffdfdfffff3fbfffffeffffffdfdfffeffffffffffff * 2 ^ 0 +
  0xa23f8d6d9aad2abab2a7d3f62d5da5bff6fffef7f75afbb2fdf9ff57ffff * 2 ^ 240 +
  0x21d4222a63f673da22271c74f35ca655f6835c2a5566abefa9b7faa3b5be * 2 ^ 480 +
  0x90e11418d4203702b9170048528a842c802340b60e221ac69817a2734df9 * 2 ^ 720 +
  0x22469014 * 2 ^ 960

@[expose]
def bits046row1 : ℕ :=
  0xfa7ff2fbff74bfbffdffff7f5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0xf95eacb8901bddfa3d91ddae3edfeddcedff2afabe9e65bfd9f6a7e67fef * 2 ^ 240 +
  0x33035353df697597a6a9095b5d443e913f9bdb8d3bc8c8d9fd6fd531198d * 2 ^ 480 +
  0x89e0e9e44032e4a28e609b922b4b18b44d07735bdd88c8c010abc5a510da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits046row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7dffffffffffffdffffffefbfffffffffffffff * 2 ^ 0 +
  0xf4b353787f5feb9dabf774ddcfe7cb6f7b1f3777b4ffbeea6ffbf35dc8f7 * 2 ^ 240 +
  0xb66b87dfd5d2ce660b73acc918f55b5aa8cf66598e72d7ad2fa2cf672859 * 2 ^ 480 +
  0x374d920089b1301544d42eaca235e1012bc88400a2158998a16355203a9a * 2 ^ 720 +
  0x110a4861 * 2 ^ 960

@[expose]
def bits046row3 : ℕ :=
  0xeffaed8dbe3ff75ffff6beffff9fffbf7ffffbdffefffefff5fffffbffff * 2 ^ 0 +
  0xaf46aff6adff7df75d6c7bedd68fde7a3fe7ffffbfdfcfff6b37cad5d7dd * 2 ^ 240 +
  0x7e328abd6c328e9c71955b25935f56300378c2f74be3d406815ff81d6b36 * 2 ^ 480 +
  0x42522503ea5c284c02b8c22544e0435712900e1b854a64f746534d88ee1e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits046 : Vector ℕ 4 := #v[bits046row0, bits046row1, bits046row2, bits046row3]

@[expose]
def bits047row0 : ℕ :=
  0x3bfffffedefd9fffffdfdfffff3fbfffffeffffffdffffffffffffffffff * 2 ^ 0 +
  0xa63f8d6d9aad2abab2b7d3f62d5da5fff6fffef7f75afbb2fdf9ff57ffff * 2 ^ 240 +
  0x21d4222a63f673da22271c76f35ca655f6835c2a5566abefa9b7faa3b5be * 2 ^ 480 +
  0x90e11418d4203702b91720685a8a842c802340b60e221ac69817e2734df9 * 2 ^ 720 +
  0x22469014 * 2 ^ 960

@[expose]
def bits047row1 : ℕ :=
  0xfa7ff2fbff74bfbffdffffff5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0xf95eacb8901bddfe3d91ddae3edfeddcefff2afabe9e65bfd9f6a7e67fef * 2 ^ 240 +
  0x33035353df697597a6a9095b5d443e913f9bdb8d3bc8c8d9fd6fd531398d * 2 ^ 480 +
  0x89e0e9e44032e4a28e609b922b4b18b44d07735bdd88c8c010bfc5a510da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits047row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b5ef7fffffffffffffdffffffefbfffffffffffffff * 2 ^ 0 +
  0xf4b353787f5feb9dabf774ddcfe7cb6ffb1f3777b4ffbefa6ffff35dc8f7 * 2 ^ 240 +
  0xb66b87dff5d2ce660b73acc918f55b5aa8df6659ce72d7ad2fa2df672859 * 2 ^ 480 +
  0x374d920089b1301544d42eaca235e1012bc88400a2158998a16355203a9a * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits047row3 : ℕ :=
  0xeffaed8dbe3ff75ffff6feffff9fffbf7ffffbdffefffefff5fffffbffff * 2 ^ 0 +
  0xaf46aff6adff7df75d6c7bedd68fde7a3fe7ffffbfdfcfff6b37cad5f7dd * 2 ^ 240 +
  0x7e328abd7c328e9c71955f25935f56300378c2f74be3d406815ff81d7b36 * 2 ^ 480 +
  0x42522503ea5c284c02b8c22544e0435712900e1b854a64f746534d88ee1e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits047 : Vector ℕ 4 := #v[bits047row0, bits047row1, bits047row2, bits047row3]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
