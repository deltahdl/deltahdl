#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

// Annex H.10.1.2 writes the canonical representation of packed arrays as the
// VPI's own vector value: the struct t_vpi_vecval of an aval and a bval word,
// with its s_vpi_vecval and p_vpi_vecval names, under the guard VPI_VECVAL --
// so that a translation unit which already holds the VPI's definition, having
// included vpi_user.h first, gets no second one from svdpi.h and the DPI's
// svLogicVecVal is that very struct. test_simulator_annex_h_10_01_02a.cpp
// takes the header's own definition; this file supplies the VPI's first, as
// such a translation unit would, and checks that svdpi.h yields to it.
#define VPI_VECVAL
typedef struct t_vpi_vecval {
  uint32_t aval;
  uint32_t bval;
} s_vpi_vecval, *p_vpi_vecval;

#include "simulator/svdpi.h"

namespace {

// §H.10.1.2: with VPI_VECVAL defined beforehand the struct is the one defined
// here, and svLogicVecVal is a chunk of exactly that type; the pointer name
// p_vpi_vecval points at it.
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

// §H.10.1.2: the 2-state chunk and the chunk count are unaffected by whose
// struct the 4-state chunk is.
TEST(SvDpiVecvalGuard, TwoStateChunkAndCountAreUnchanged) {
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
}

}  // namespace
