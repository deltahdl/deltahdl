#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

svLogicVecVal g_f1_arr[SV_PACKED_DATA_NELEMS(128)] = {};
std::vector<uint32_t> g_f2_last_chunks;

void F1(const svLogicVecVal* packed_vec_128_bit) {
  svLogicVecVal arr[SV_PACKED_DATA_NELEMS(128)];
  memcpy(arr, packed_vec_128_bit, sizeof(arr));
  memcpy(g_f1_arr, arr, sizeof(arr));
}

void F2(svOpenArrayHandle h) {
  int i = 0;
  svLogicVecVal arr[SV_PACKED_DATA_NELEMS(128)];
  g_f2_last_chunks.clear();
  for (i = svLow(h, 1); i <= svHigh(h, 1); i++) {
    const auto* ptr = static_cast<const svLogicVecVal*>(svGetArrElemPtr1(h, i));
    memcpy(arr, ptr, sizeof(arr));
    g_f2_last_chunks.push_back(arr[3].aval);
  }
}

TEST(DpiPackedArrayAccessExample, TheTwoFormalsAreACanonicalPointerAndAHandle) {
  DpiArg vec;
  vec.name = "packed_vec_128_bit";
  vec.type = DataTypeKind::kLogic;
  vec.width = 128;
  vec.direction = Direction::kInput;
  EXPECT_EQ(DpiCTypeOfFormal(vec, false), "const svLogicVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(vec, true), "const svOpenArrayHandle");
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(128), 4);
  EXPECT_EQ(DpiCanonicalWordCount(128), 4u);
}

TEST(DpiPackedArrayAccessExample, F1CopiesTheFourChunksOfItsVector) {
  const svLogicVecVal kVector[SV_PACKED_DATA_NELEMS(128)] = {
      {0x11111111u, 0}, {0x22222222u, 0xF}, {0x33333333u, 0}, {0x44444444u, 1}};
  F1(kVector);
  for (std::size_t k = 0; k < 4; ++k) {
    EXPECT_EQ(g_f1_arr[k].aval, kVector[k].aval) << k;
    EXPECT_EQ(g_f1_arr[k].bval, kVector[k].bval) << k;
  }
}

TEST(DpiPackedArrayAccessExample, F2CopiesEachElementOfTheOpenArrayByItsIndex) {
  svLogicVecVal data[3][SV_PACKED_DATA_NELEMS(128)] = {};
  for (std::size_t e = 0; e < 3; ++e) {
    for (std::size_t k = 0; k < 4; ++k) {
      data[e][k].aval = static_cast<uint32_t>(100 * e + k);
    }
  }
  const SvOpenArrayDimRange kRanges[] = {{127, 0}, {5, 3}};
  SvOpenArrayDesc desc;
  desc.data = data;
  desc.n_dims = 2;
  desc.has_packed_part = 1;
  desc.ranges = kRanges;
  desc.elem_size = sizeof(data[0]);
  F2(&desc);
  ASSERT_EQ(g_f2_last_chunks.size(), 3u);
  EXPECT_EQ(g_f2_last_chunks[0], 203u);
  EXPECT_EQ(g_f2_last_chunks[1], 103u);
  EXPECT_EQ(g_f2_last_chunks[2], 3u);
}

}  // namespace
