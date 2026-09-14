#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

// §H.12.10, the C side of Example 8, compiled against this svdpi.h as the
// example writes it -- under the names this tree's naming rules give C++
// code, F1 and F2 for f1 and f2, and without the const the example puts on
// the handle parameter, which those rules read as a constant: f1 copies its
// one 128-bit packed vector out of the canonical representation it is
// passed by reference to, into a canonical array of SV_PACKED_DATA_NELEMS
// (128) chunks; f2 copies each element of an open array of such vectors out
// through the address svGetArrElemPtr1 computes for it, by the array's own
// indices.

// What the copies yielded: the chunks f1 copied, and the last chunk of every
// element f2 copied, in the order it visited them.
svLogicVecVal g_f1_arr[SV_PACKED_DATA_NELEMS(128)] = {};
std::vector<uint32_t> g_f2_last_chunks;

/* Copy out one 128-bit packed vector */
void F1(const svLogicVecVal* packed_vec_128_bit) {
  svLogicVecVal arr[SV_PACKED_DATA_NELEMS(128)]; /* canonical rep */
  memcpy(arr, packed_vec_128_bit, sizeof(arr));
  memcpy(g_f1_arr, arr, sizeof(arr));
}

/* Copy out each word of an open array of 128-bit packed vectors */
void F2(svOpenArrayHandle h) {
  int i = 0;
  svLogicVecVal arr[SV_PACKED_DATA_NELEMS(128)]; /* canonical rep */
  g_f2_last_chunks.clear();
  for (i = svLow(h, 1); i <= svHigh(h, 1); i++) {
    const auto* ptr = static_cast<const svLogicVecVal*>(svGetArrElemPtr1(h, i));
    memcpy(arr, ptr, sizeof(arr));
    g_f2_last_chunks.push_back(arr[3].aval);
  }
}

// §H.12.10 with §H.8.4 and §H.8.6: f1's formal is the 128-bit vector by
// reference to its canonical representation, const svLogicVecVal*, four
// chunks wide, and f2's is the open array's handle.
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

// f1 over a 128-bit vector whose four chunks carry distinct avals and
// bvals: the copy in arr is chunk for chunk the vector passed.
TEST(DpiPackedArrayAccessExample, F1CopiesTheFourChunksOfItsVector) {
  const svLogicVecVal kVector[SV_PACKED_DATA_NELEMS(128)] = {
      {0x11111111u, 0}, {0x22222222u, 0xF}, {0x33333333u, 0}, {0x44444444u, 1}};
  F1(kVector);
  for (std::size_t k = 0; k < 4; ++k) {
    EXPECT_EQ(g_f1_arr[k].aval, kVector[k].aval) << k;
    EXPECT_EQ(g_f1_arr[k].bval, kVector[k].bval) << k;
  }
}

// f2 over an open array of three 128-bit vectors [5:3], each element's
// chunks held in the canonical form the handle's descriptor describes: the
// elements are visited from 3 to 5 by the array's own indices, and the copy
// of each is that element's.
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
  desc.ranges = kRanges;
  desc.elem_size = sizeof(data[0]);
  F2(&desc);
  // Index 5 is the left bound and so the first element in storage, index 3
  // the last: visiting 3, 4, 5 reads the elements stored third, second and
  // first.
  ASSERT_EQ(g_f2_last_chunks.size(), 3u);
  EXPECT_EQ(g_f2_last_chunks[0], 203u);
  EXPECT_EQ(g_f2_last_chunks[1], 103u);
  EXPECT_EQ(g_f2_last_chunks[2], 3u);
}

}  // namespace
