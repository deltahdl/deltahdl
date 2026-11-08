#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#define VPI_VECVAL
typedef struct t_vpi_vecval {
  uint32_t aval;
  uint32_t bval;
} s_vpi_vecval, *p_vpi_vecval;

#include "simulator/svdpi.h"

namespace {

TEST(SvDpiVecvalGuard, HeaderYieldsToAPriorVpiDefinition) {
  EXPECT_TRUE((std::is_same<svLogicVecVal, s_vpi_vecval>::value));
  EXPECT_TRUE((std::is_same<p_vpi_vecval, s_vpi_vecval*>::value));
  s_vpi_vecval chunk;
  chunk.aval = 0x0000FFFFu;
  chunk.bval = 0xFFFF0000u;
  p_vpi_vecval p = &chunk;
  svLogicVecVal* q = &chunk;
  EXPECT_EQ(p->aval, 0x0000FFFFu);
  EXPECT_EQ(q->bval, 0xFFFF0000u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

TEST(SvDpiVecvalGuard, TwoStateChunkAndCountAreUnchanged) {
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
}

}  // namespace
