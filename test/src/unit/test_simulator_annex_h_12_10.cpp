#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
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

void SeeFourChunks(const svLogicVecVal* v) {
  SeeInC({v[0].aval, v[1].aval, v[1].bval, v[2].aval, v[3].aval, v[3].bval});
}

void SeeElementsOf128Bits(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    svLogicVecVal arr[SV_PACKED_DATA_NELEMS(128)] = {};
    svGetLogicArrElem1VecVal(arr, h, i);
    for (const svLogicVecVal& chunk : arr) {
      SeeInC({chunk.aval});
      SeeInC({chunk.bval});
    }
    const auto* ptr = static_cast<const svLogicVecVal*>(svGetArrElemPtr1(h, i));
    bool agrees = ptr == nullptr || memcmp(ptr, arr, sizeof(arr)) == 0;
    SeeInC({agrees ? 1 : 0});
  }
}

TEST(DpiPackedArrayAccessExample, ADesignsVectorArrivesAsFourChunks) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void f1(input logic [127:0]);\n"
      "  logic [127:0] v;\n"
      "  initial begin\n"
      "    v = {32'h8x00_0001, 32'h2, 32'hz000_0003, 32'h4};\n"
      "    f1(v);\n"
      "  end\n",
      f, {{"f1", CAddress(&SeeFourChunks)}}, "annex_h_12_10_vector");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{4, 3, 0xF0000000, 2, 0x8F000001,
                                               0x0F000000}));
}

TEST(DpiPackedArrayAccessExample, ADesignsOpenArrayOfVectorsIsCopiedOut) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void f2(input logic [127:0] i []);\n"
      "  logic [127:0] v [5:4];\n"
      "  initial begin\n"
      "    v[4] = {32'h1, 32'h2, 32'hz000_0003, 32'h4};\n"
      "    v[5] = {32'h5, 32'hx, 32'h7, 32'h8};\n"
      "    f2(v);\n"
      "  end\n",
      f, {{"f2", CAddress(&SeeElementsOf128Bits)}}, "annex_h_12_10_open");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{4, 0, 3, 0xF0000000, 2, 0, 1, 0, 1, 8, 0, 7,
                                    0, 0xFFFFFFFF, 0xFFFFFFFF, 5, 0, 1}));
}

}  // namespace
