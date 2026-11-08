#include <gtest/gtest.h>

#include <array>

#include "parser/ast_type.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

TEST(DpiOtherElementTypes, CCompatibleElementsNeedNoCanonicalRepresentation) {
  EXPECT_FALSE(
      DpiCanonicalRepresentationIsNeededForElement(DataTypeKind::kInt, 0));
  EXPECT_FALSE(
      DpiCanonicalRepresentationIsNeededForElement(DataTypeKind::kReal, 0));
  EXPECT_FALSE(
      DpiCanonicalRepresentationIsNeededForElement(DataTypeKind::kStruct, 0));
  EXPECT_FALSE(
      DpiCanonicalRepresentationIsNeededForElement(DataTypeKind::kBit, 1));
  EXPECT_TRUE(
      DpiCanonicalRepresentationIsNeededForElement(DataTypeKind::kBit, 8));
  EXPECT_TRUE(
      DpiCanonicalRepresentationIsNeededForElement(DataTypeKind::kLogic, 64));
}

TEST(DpiOtherElementTypes, TheAddressIsComputedFirstAndThenUsed) {
  const std::array<DpiPointerAccessStep, 2> kSteps = DpiPointerAccessSteps();
  EXPECT_EQ(kSteps[0], DpiPointerAccessStep::kComputeTheElementsAddress);
  EXPECT_EQ(kSteps[1], DpiPointerAccessStep::kAccessTheElementThroughIt);
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kInt, 0),
            DpiElementAccessMethod::kGenericPointerWithCasting);
}

TEST(DpiOtherElementTypes, AnIntElementIsReachedThroughItsComputedAddress) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {2, 1}, {-1, -2}};
  int data[2][2] = {{10, 11}, {12, 13}};
  SvOpenArrayDesc desc;
  desc.data = data;
  desc.n_dims = 3;
  desc.has_packed_part = 1;
  desc.ranges = kRanges;
  desc.elem_size = sizeof(int);
  svOpenArrayHandle h = &desc;

  void* address = svGetArrElemPtr2(h, 1, -2);
  ASSERT_NE(address, nullptr);
  auto* element = static_cast<int*>(address);
  EXPECT_EQ(*element, 13);
  *element = 42;
  EXPECT_EQ(data[1][1], 42);

  void* first = svGetArrElemPtr2(h, 2, -1);
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(*static_cast<int*>(first), 10);
}

}  // namespace
