#include <gtest/gtest.h>

#include "simulator/svdpi.h"

// Annex H.12.4 - Access to actual representation.
//
// H.12.4 defines the DPI C-layer functions that hand back the actual address of
// an open array or of its individual elements. Its normative requirements are:
//
//   C1 - svGetArrElemPtr/1/2/3 return the address of an individual element, and
//        such per-element access shall always be supported;
//   C2 - if the SystemVerilog array layout differs from the C layout, the address
//        and size of the array as a whole shall be undefined (0); svGetArrayPtr
//        returns a null pointer and svSizeOfArray returns 0;
//   C3 - the element functions shall return a null pointer when the element's
//        representation differs from that of an individual value of the same type
//        (modeled here by a zero element stride), and likewise for an
//        out-of-range index, a null handle, or a mismatched index count.
//
// These tests build an svOpenArrayHandle backed by a real svOpenArrayDesc buffer
// and observe the svdpi.cpp functions applying those rules. The descriptor's
// dimension 0 describes the single packed part (H.12.2) and dimensions above 0
// the unpacked part; elem_size records the per-element byte stride of the actual
// representation.

namespace {

svOpenArrayHandle MakeHandle(void* data, const svOpenArrayDimRange* ranges,
                             int n_dims, size_t elem_size,
                             svOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->ranges = ranges;
  desc->elem_size = elem_size;
  return desc;
}

// C1: each unpacked index resolves to the element's own slot in storage. The
// handle models: bit [7:0] arr [0:3], one canonical word per element.
TEST(ActualRepresentation, ElementAddress1D) {
  const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, ranges, 2, sizeof(svBitVecVal), &desc);

  for (int i = 0; i < 4; ++i)
    EXPECT_EQ(svGetArrElemPtr1(h, i), static_cast<void*>(&data[i]));
}

// C1: indexing follows the actual argument's original SystemVerilog range. For a
// descending unpacked range [3:1], the left bound (index 3) occupies position 0
// and positions advance toward the right bound, so index 1 lands two slots in.
TEST(ActualRepresentation, ElementAddressDescendingRange) {
  const svOpenArrayDimRange ranges[] = {{7, 0}, {3, 1}};
  svBitVecVal data[3] = {0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, ranges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 3), static_cast<void*>(&data[0]));
  EXPECT_EQ(svGetArrElemPtr1(h, 2), static_cast<void*>(&data[1]));
  EXPECT_EQ(svGetArrElemPtr1(h, 1), static_cast<void*>(&data[2]));
}

// C1: a multi-word packed element widens the stride between elements. The handle
// models bit [39:0] arr [0:2]: two canonical words (8 bytes) per element.
TEST(ActualRepresentation, ElementAddressMultiWordStride) {
  const svOpenArrayDimRange ranges[] = {{39, 0}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  const size_t stride = 2 * sizeof(svBitVecVal);
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, stride, &desc);

  char* base = reinterpret_cast<char*>(data);
  EXPECT_EQ(svGetArrElemPtr1(h, 0), static_cast<void*>(base + 0 * stride));
  EXPECT_EQ(svGetArrElemPtr1(h, 1), static_cast<void*>(base + 1 * stride));
  EXPECT_EQ(svGetArrElemPtr1(h, 2), static_cast<void*>(base + 2 * stride));
}

// C1: two and three unpacked indices select an element row-major over the
// unpacked dimensions. Handle: bit [7:0] arr [0:1][0:2] (then [0:1] added).
TEST(ActualRepresentation, ElementAddress2DAnd3DRowMajor) {
  {
    const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 1}, {0, 2}};
    svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
    svOpenArrayDesc desc;
    svOpenArrayHandle h =
        MakeHandle(data, ranges, 3, sizeof(svBitVecVal), &desc);
    // Row-major: linear = i*3 + j.
    EXPECT_EQ(svGetArrElemPtr2(h, 0, 0), static_cast<void*>(&data[0]));
    EXPECT_EQ(svGetArrElemPtr2(h, 0, 2), static_cast<void*>(&data[2]));
    EXPECT_EQ(svGetArrElemPtr2(h, 1, 0), static_cast<void*>(&data[3]));
    EXPECT_EQ(svGetArrElemPtr2(h, 1, 2), static_cast<void*>(&data[5]));
  }
  {
    const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 1}, {0, 1}, {0, 1}};
    svBitVecVal data[8];
    for (int i = 0; i < 8; ++i) data[i] = 0;
    svOpenArrayDesc desc;
    svOpenArrayHandle h =
        MakeHandle(data, ranges, 4, sizeof(svBitVecVal), &desc);
    // Row-major: linear = ((i*2)+j)*2 + k.
    EXPECT_EQ(svGetArrElemPtr3(h, 0, 0, 0), static_cast<void*>(&data[0]));
    EXPECT_EQ(svGetArrElemPtr3(h, 0, 1, 1), static_cast<void*>(&data[3]));
    EXPECT_EQ(svGetArrElemPtr3(h, 1, 0, 1), static_cast<void*>(&data[5]));
    EXPECT_EQ(svGetArrElemPtr3(h, 1, 1, 1), static_cast<void*>(&data[7]));
  }
}

// C1: the general variadic entry point gathers one index per unpacked dimension
// and resolves to the same address as the specialized functions.
TEST(ActualRepresentation, VariadicMatchesSpecialized) {
  const svOpenArrayDimRange ranges1[] = {{7, 0}, {0, 3}};
  svBitVecVal data1[4] = {0, 0, 0, 0};
  svOpenArrayDesc desc1;
  svOpenArrayHandle h1 =
      MakeHandle(data1, ranges1, 2, sizeof(svBitVecVal), &desc1);
  for (int i = 0; i < 4; ++i)
    EXPECT_EQ(svGetArrElemPtr(h1, i), svGetArrElemPtr1(h1, i));

  const svOpenArrayDimRange ranges2[] = {{7, 0}, {0, 1}, {0, 2}};
  svBitVecVal data2[6] = {0, 0, 0, 0, 0, 0};
  svOpenArrayDesc desc2;
  svOpenArrayHandle h2 =
      MakeHandle(data2, ranges2, 3, sizeof(svBitVecVal), &desc2);
  for (int i = 0; i < 2; ++i)
    for (int j = 0; j < 3; ++j)
      EXPECT_EQ(svGetArrElemPtr(h2, i, j), svGetArrElemPtr2(h2, i, j));
}

// C2: the whole-array address and size are undefined because the simulator's
// canonical storage layout differs from the C layout; they are pinned to 0.
TEST(ActualRepresentation, WholeArrayAddressAndSizeUndefined) {
  const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, ranges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrayPtr(h), nullptr);
  EXPECT_EQ(svSizeOfArray(h), 0);
}

// C3: an index outside the element's original range yields a null pointer.
TEST(ActualRepresentation, OutOfRangeIndexReturnsNull) {
  const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, ranges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr1(h, 4), nullptr);
}

// C3: a null handle and a mismatched index count both yield a null pointer.
TEST(ActualRepresentation, NullHandleAndWrongIndexCountReturnNull) {
  EXPECT_EQ(svGetArrElemPtr1(nullptr, 0), nullptr);

  const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, ranges, 2, sizeof(svBitVecVal), &desc);

  // The array has one unpacked dimension, so two indices is a mismatch.
  EXPECT_EQ(svGetArrElemPtr2(h, 0, 0), nullptr);
}

// C3: a zero element stride marks an element representation that differs from an
// individual value of the same type, so element access returns a null pointer.
TEST(ActualRepresentation, RepresentationDiffersReturnsNull) {
  const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, /*elem_size=*/0, &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 0), nullptr);
}

// C1/C3: a handle whose backing storage pointer is null has no element to
// address, so element access returns a null pointer even when the handle and
// index are otherwise valid. This is the listing's "null pointer" case, distinct
// from passing a null handle.
TEST(ActualRepresentation, NullArrayPointerReturnsNull) {
  const svOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(/*data=*/nullptr, ranges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 0), nullptr);
}

}  // namespace
