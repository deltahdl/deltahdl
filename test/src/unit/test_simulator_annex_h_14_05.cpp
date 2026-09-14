#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/svdpi_src.h"

namespace {

// §H.14.5, the C side of Example 10, compiled against svdpi.h and svdpi_src.h
// as the example writes it -- under the names this tree's naming rules give
// C++ code, Triple for the example's triple typedef, F1 for f1 and
// ExportedSvFunc for exported_sv_func: a struct mixing C types with a member
// b declared by SV_BIT_PACKED_ARRAY in the implementation-specific
// representation, as for bit [6*8-1:0] b [63:0], the extern the export is
// called through with an svLogicPackedArrRef, and f1 reading each word of b
// into a canonical buffer by svGetBitVec32, calling the export with a
// variable SV_LOGIC_PACKED_ARRAY declares passed by reference, and reading
// that variable into a canonical buffer by svGetLogicVec32.
struct Triple {
  int a;
  SV_BIT_PACKED_ARRAY(6 * 8, b)
  [64]; /* implementation-specific representation */
  int c;
};

// What the example's SystemVerilog function does is elided; this stand-in
// records what it was handed and writes both chunks of its 64-bit output.
int g_exported_sv_func_i = 0;
void ExportedSvFunc(int i, svLogicPackedArrRef o) {
  g_exported_sv_func_i = i;
  const svLogicVec32 kValue[2] = {{static_cast<unsigned int>(i), 0u},
                                  {static_cast<unsigned int>(i) * 2u, 0u}};
  svPutLogicVec32(o, kValue, 64);
}

// The bytes f1 read out of b, summed, and the canonical copy of the output.
uint32_t g_sum_of_low_bytes = 0;
svLogicVec32 g_al[SV_CANONICAL_SIZE(64)] = {};

void F1(const Triple* t) {
  /* canonical representation */
  svBitVec32 a_b[SV_CANONICAL_SIZE(6 * 8)]; /* 6*8 packed bits */
  svLogicVec32 a_l[SV_CANONICAL_SIZE(64)];
  /* implementation-specific representation */
  SV_LOGIC_PACKED_ARRAY(64, my_tab);
  g_sum_of_low_bytes = 0;
  for (int i = 0; i < 64; i++) {
    svGetBitVec32(a_b, const_cast<void*>(static_cast<const void*>(&(t->b[i]))),
                  6 * 8);
    g_sum_of_low_bytes += a_b[0] & 0xFFu;
  }
  /* call SystemVerilog */
  ExportedSvFunc(2, &my_tab); /* by reference */
  svGetLogicVec32(a_l, &my_tab, 64);
  g_al[0] = a_l[0];
  g_al[1] = a_l[1];
}

// §H.14.5 with §H.14.3: the member b the macro declares is 64 elements of
// two chunks each, sized as the simulator's representation of 48 bits, and
// no array type stands between the element and the reference taken to it.
TEST(DpiSourceCompatibleExample,
     TheMemberIsDeclaredInTheImplementationsRepresentation) {
  Triple t = {};
  EXPECT_EQ(sizeof(t.b[0]), static_cast<size_t>(svSizeOfBitPackedArr(6 * 8)));
  EXPECT_EQ(sizeof(t.b) / sizeof(t.b[0]), 64u);
  EXPECT_EQ(SV_CANONICAL_SIZE(6 * 8), 2);
}

// f1 run over a triple whose word i of b holds i + 1 in its least
// significant byte: the canonical copies of the 64 words sum their low bytes
// to 2080, the export was called with 2, and the canonical copy of my_tab
// holds the two chunks the export put.
TEST(DpiSourceCompatibleExample,
     F1ReadsEveryWordAndTheExportsOutputThroughReferences) {
  Triple t = {};
  t.a = 1;
  t.c = 3;
  for (int i = 0; i < 64; i++) {
    t.b[i].chunks[0] =
        (static_cast<uint32_t>(i) << 8) | static_cast<uint32_t>(i + 1);
    t.b[i].chunks[1] = 0xFFFFu;
  }
  F1(&t);
  EXPECT_EQ(g_sum_of_low_bytes, 2080u);
  EXPECT_EQ(g_exported_sv_func_i, 2);
  EXPECT_EQ(g_al[0].c, 2u);
  EXPECT_EQ(g_al[1].c, 4u);
  EXPECT_EQ(g_al[0].d + g_al[1].d, 0u);
}

}  // namespace
