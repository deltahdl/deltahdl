#include <gtest/gtest.h>

#include <cstddef>
#include <type_traits>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

svOpenArrayHandle MakeHandle(void* data, const SvOpenArrayDimRange* ranges,
                             int n_dims, size_t elem_size,
                             SvOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->has_packed_part = 1;
  desc->ranges = ranges;
  desc->elem_size = elem_size;
  return desc;
}

TEST(ActualRepresentation, ElementAddress1D) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, kRanges, 2, sizeof(svBitVecVal), &desc);

  for (int i = 0; i < 4; ++i)
    EXPECT_EQ(svGetArrElemPtr1(h, i), static_cast<void*>(&data[i]));
}

TEST(ActualRepresentation, ElementAddressDescendingRange) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {3, 1}};
  svBitVecVal data[3] = {0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, kRanges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 3), static_cast<void*>(&data[0]));
  EXPECT_EQ(svGetArrElemPtr1(h, 2), static_cast<void*>(&data[1]));
  EXPECT_EQ(svGetArrElemPtr1(h, 1), static_cast<void*>(&data[2]));
}

TEST(ActualRepresentation, ElementAddressMultiWordStride) {
  const SvOpenArrayDimRange kRanges[] = {{39, 0}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  const size_t kStride = 2 * sizeof(svBitVecVal);
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, kStride, &desc);

  char* base = reinterpret_cast<char*>(data);
  EXPECT_EQ(svGetArrElemPtr1(h, 0), static_cast<void*>(base + 0 * kStride));
  EXPECT_EQ(svGetArrElemPtr1(h, 1), static_cast<void*>(base + 1 * kStride));
  EXPECT_EQ(svGetArrElemPtr1(h, 2), static_cast<void*>(base + 2 * kStride));
}

TEST(ActualRepresentation, ElementAddress2DAnd3DRowMajor) {
  {
    const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 1}, {0, 2}};
    svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
    SvOpenArrayDesc desc;
    svOpenArrayHandle h =
        MakeHandle(data, kRanges, 3, sizeof(svBitVecVal), &desc);
    EXPECT_EQ(svGetArrElemPtr2(h, 0, 0), static_cast<void*>(&data[0]));
    EXPECT_EQ(svGetArrElemPtr2(h, 0, 2), static_cast<void*>(&data[2]));
    EXPECT_EQ(svGetArrElemPtr2(h, 1, 0), static_cast<void*>(&data[3]));
    EXPECT_EQ(svGetArrElemPtr2(h, 1, 2), static_cast<void*>(&data[5]));
  }
  {
    const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 1}, {0, 1}, {0, 1}};
    svBitVecVal data[8];
    for (int i = 0; i < 8; ++i) data[i] = 0;
    SvOpenArrayDesc desc;
    svOpenArrayHandle h =
        MakeHandle(data, kRanges, 4, sizeof(svBitVecVal), &desc);
    EXPECT_EQ(svGetArrElemPtr3(h, 0, 0, 0), static_cast<void*>(&data[0]));
    EXPECT_EQ(svGetArrElemPtr3(h, 0, 1, 1), static_cast<void*>(&data[3]));
    EXPECT_EQ(svGetArrElemPtr3(h, 1, 0, 1), static_cast<void*>(&data[5]));
    EXPECT_EQ(svGetArrElemPtr3(h, 1, 1, 1), static_cast<void*>(&data[7]));
  }
}

TEST(ActualRepresentation, VariadicMatchesSpecialized) {
  const SvOpenArrayDimRange kRanges1[] = {{7, 0}, {0, 3}};
  svBitVecVal data1[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc1;
  svOpenArrayHandle h1 =
      MakeHandle(data1, kRanges1, 2, sizeof(svBitVecVal), &desc1);
  for (int i = 0; i < 4; ++i)
    EXPECT_EQ(svGetArrElemPtr(h1, i), svGetArrElemPtr1(h1, i));

  const SvOpenArrayDimRange kRanges2[] = {{7, 0}, {0, 1}, {0, 2}};
  svBitVecVal data2[6] = {0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc2;
  svOpenArrayHandle h2 =
      MakeHandle(data2, kRanges2, 3, sizeof(svBitVecVal), &desc2);
  for (int i = 0; i < 2; ++i)
    for (int j = 0; j < 3; ++j)
      EXPECT_EQ(svGetArrElemPtr(h2, i, j), svGetArrElemPtr2(h2, i, j));
}

TEST(ActualRepresentation, WholeArrayAddressAndSizeUndefined) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, kRanges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrayPtr(h), nullptr);
  EXPECT_EQ(svSizeOfArray(h), 0);
}

TEST(ActualRepresentation, OutOfRangeIndexReturnsNull) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, kRanges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr1(h, 4), nullptr);
}

TEST(ActualRepresentation, NullHandleAndWrongIndexCountReturnNull) {
  EXPECT_EQ(svGetArrElemPtr1(nullptr, 0), nullptr);

  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(data, kRanges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrElemPtr2(h, 0, 0), nullptr);
}

TEST(ActualRepresentation, RepresentationDiffersReturnsNull) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, 0, &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 0), nullptr);
}

TEST(ActualRepresentation, NullArrayPointerReturnsNull) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h =
      MakeHandle(nullptr, kRanges, 2, sizeof(svBitVecVal), &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 0), nullptr);
}

TEST(DpiActualRepresentationModel, TheAccessMethodFollowsTheElementsType) {
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kBit, 8),
            DpiElementAccessMethod::kCopyingToOrFromCanonical);
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kLogic, 64),
            DpiElementAccessMethod::kCopyingToOrFromCanonical);
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kBit, 1),
            DpiElementAccessMethod::kDirectly);
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kLogic, 1),
            DpiElementAccessMethod::kDirectly);
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kInt, 0),
            DpiElementAccessMethod::kGenericPointerWithCasting);
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kStruct, 0),
            DpiElementAccessMethod::kGenericPointerWithCasting);
}

TEST(DpiActualRepresentationModel,
     PointerAccessIsPerArrayAndIndexingIsSpecializedToThree) {
  EXPECT_TRUE(DpiScalarOrPackedElementIsAccessibleByPointer(true));
  EXPECT_FALSE(DpiScalarOrPackedElementIsAccessibleByPointer(false));
  EXPECT_TRUE(DpiIndexingFunctionIsSpecializedFor(1));
  EXPECT_TRUE(DpiIndexingFunctionIsSpecializedFor(2));
  EXPECT_TRUE(DpiIndexingFunctionIsSpecializedFor(3));
  EXPECT_FALSE(DpiIndexingFunctionIsSpecializedFor(4));
  EXPECT_FALSE(DpiIndexingFunctionIsSpecializedFor(0));
}

TEST(DpiActualRepresentationModel, TheWholeArrayNeedsTheCLayoutAnElementNever) {
  EXPECT_TRUE(DpiWholeArrayIsAccessible(true));
  EXPECT_FALSE(DpiWholeArrayIsAccessible(false));
  EXPECT_TRUE(DpiElementAddressIsAlwaysSupported());
  EXPECT_EQ(DpiAddressFunctionPointerType(), "void*");
  EXPECT_TRUE((std::is_same<decltype(svGetArrayPtr(nullptr)), void*>::value));
  EXPECT_TRUE(
      (std::is_same<decltype(svGetArrElemPtr1(nullptr, 0)), void*>::value));
}

TEST(DpiActualRepresentationModel,
     AnElementPointerNeedsTheIndividualValuesRepresentation) {
  EXPECT_TRUE(DpiElementPointerIsMeaningful(true));
  EXPECT_FALSE(DpiElementPointerIsMeaningful(false));
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {1, 2, 3, 4};
  SvOpenArrayDesc same;
  svOpenArrayHandle as_values =
      MakeHandle(data, kRanges, 2, sizeof(svBitVecVal), &same);
  EXPECT_EQ(*static_cast<svBitVecVal*>(svGetArrElemPtr1(as_values, 3)), 4u);
  SvOpenArrayDesc compacted;
  svOpenArrayHandle differing = MakeHandle(data, kRanges, 2, 0, &compacted);
  EXPECT_EQ(svGetArrElemPtr1(differing, 3), nullptr);
}

TEST(ActualRepresentation, AnIndexOutsideAnyOfTwoDimensionsGivesNull) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {11, 12}, {1, -1}};
  int data[6] = {};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, sizeof(int), &desc);
  EXPECT_EQ(svGetArrElemPtr2(h, 12, -1), static_cast<void*>(&data[5]));
  EXPECT_EQ(svGetArrElemPtr(h, 12, -1), static_cast<void*>(&data[5]));
  EXPECT_EQ(svGetArrElemPtr2(h, 10, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr2(h, 13, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr2(h, 11, 2), nullptr);
  EXPECT_EQ(svGetArrElemPtr2(h, 11, -2), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 10, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 13, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 11, 2), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 11, -2), nullptr);
}

TEST(ActualRepresentation, AnIndexOutsideAnyOfThreeDimensionsGivesNull) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {3, 2}, {5, 6}, {-1, -2}};
  int data[8] = {};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 4, sizeof(int), &desc);
  EXPECT_EQ(svGetArrElemPtr3(h, 2, 6, -2), static_cast<void*>(&data[7]));
  EXPECT_EQ(svGetArrElemPtr(h, 2, 6, -2), static_cast<void*>(&data[7]));
  EXPECT_EQ(svGetArrElemPtr3(h, 4, 5, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr3(h, 1, 5, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr3(h, 2, 4, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr3(h, 2, 7, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr3(h, 2, 5, 0), nullptr);
  EXPECT_EQ(svGetArrElemPtr3(h, 2, 5, -3), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 4, 5, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 2, 7, -1), nullptr);
  EXPECT_EQ(svGetArrElemPtr(h, 2, 5, -3), nullptr);
}

void SeeWhatLiesOutside(svOpenArrayHandle h) {
  SeeInC({static_cast<long long>(svGetArrElemPtr2(h, 11, 1) != nullptr),
          static_cast<long long>(svGetArrElemPtr2(h, 99, 0) != nullptr),
          static_cast<long long>(svGetArrElemPtr2(h, 11, 99) != nullptr),
          static_cast<long long>(svGetArrElemPtr(h, 11, 99) != nullptr)});
}

TEST(ActualRepresentation, ADesignsElementOutsideItsRangesHasNoAddress) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input int a [][]);\n"
      "  int m [11:12][0:1];\n"
      "  initial see(m);\n",
      f, {{"see", CAddress(&SeeWhatLiesOutside)}}, "annex_h_12_04_outside");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 0, 0, 0}));
}

TEST(ActualRepresentation, DISABLED_AnArrayInCLayoutHasAnAddressAndASize) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {1, 3}, {0, 1}};
  int data[6] = {};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, sizeof(int), &desc);
  EXPECT_EQ(svGetArrayPtr(h), static_cast<void*>(data));
  EXPECT_EQ(svSizeOfArray(h), 24);
}

void SeeTheWholeArrayOfInts(svOpenArrayHandle h) {
  const auto* whole = static_cast<const int*>(svGetArrayPtr(h));
  if (whole == nullptr) {
    SeeInC({0, svSizeOfArray(h)});
    return;
  }
  SeeInC({whole[0], whole[2], svSizeOfArray(h)});
}

TEST(ActualRepresentation, DISABLED_ADesignsArrayOfIntsHasAnAddress) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input int a []);\n"
      "  int x [3:1];\n"
      "  initial begin\n"
      "    x[3] = 30; x[2] = 20; x[1] = 10;\n"
      "    see(x);\n"
      "  end\n",
      f, {{"see", CAddress(&SeeTheWholeArrayOfInts)}}, "annex_h_12_04_whole");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{10, 30, 12}));
}

TEST(ActualRepresentation, TheAddressFunctionsHaveTheirPrototypes) {
  EXPECT_TRUE(
      (std::is_same_v<decltype(svGetArrayPtr), void*(svOpenArrayHandle)>));
  EXPECT_TRUE(
      (std::is_same_v<decltype(svSizeOfArray), int(svOpenArrayHandle)>));
  EXPECT_TRUE((std::is_same_v<decltype(svGetArrElemPtr),
                              void*(svOpenArrayHandle, int, ...)>));
  EXPECT_TRUE((std::is_same_v<decltype(svGetArrElemPtr1),
                              void*(svOpenArrayHandle, int)>));
  EXPECT_TRUE((std::is_same_v<decltype(svGetArrElemPtr2),
                              void*(svOpenArrayHandle, int, int)>));
  EXPECT_TRUE((std::is_same_v<decltype(svGetArrElemPtr3),
                              void*(svOpenArrayHandle, int, int, int)>));
}

}  // namespace
