#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>

#include "simulator/svdpi_src.h"
#include "simulator/svdpi_sv31a.h"

namespace {

struct Triple {
  int a;
  SV_BIT_PACKED_ARRAY(6 * 8, b)
  [64];
  int c;
};

int g_exported_sv_func_i = 0;
void ExportedSvFunc(int i, svLogicPackedArrRef o) {
  g_exported_sv_func_i = i;
  const svLogicVec32 kValue[2] = {{static_cast<unsigned int>(i), 0u},
                                  {static_cast<unsigned int>(i) * 2u, 0u}};
  svPutLogicVec32(o, kValue, 64);
}

uint32_t g_sum_of_low_bytes = 0;
svLogicVec32 g_al[SV_CANONICAL_SIZE(64)] = {};

void F1(const Triple* t) {
  svBitVec32 a_b[SV_CANONICAL_SIZE(6 * 8)];
  svLogicVec32 a_l[SV_CANONICAL_SIZE(64)];
  SV_LOGIC_PACKED_ARRAY(64, my_tab);
  g_sum_of_low_bytes = 0;
  for (int i = 0; i < 64; i++) {
    svGetBitVec32(a_b, const_cast<void*>(static_cast<const void*>(&(t->b[i]))),
                  6 * 8);
    g_sum_of_low_bytes += a_b[0] & 0xFFu;
  }
  ExportedSvFunc(2, &my_tab);
  svGetLogicVec32(a_l, &my_tab, 64);
  g_al[0] = a_l[0];
  g_al[1] = a_l[1];
}

TEST(DpiSourceCompatibleExample,
     TheMemberIsDeclaredInTheImplementationsRepresentation) {
  Triple t = {};
  EXPECT_EQ(sizeof(t.b[0]), static_cast<size_t>(svSizeOfBitPackedArr(6 * 8)));
  EXPECT_EQ(sizeof(t.b) / sizeof(t.b[0]), 64u);
  EXPECT_EQ(SV_CANONICAL_SIZE(6 * 8), 2);
}

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
