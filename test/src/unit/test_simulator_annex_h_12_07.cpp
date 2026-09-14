#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>

#include "parser/ast.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

// §H.12.7: an array whose elements are of a type compatible with C has no
// need of the canonical representation, which a packed array element does
// need; a scalar bit or logic has its own functions and needs it neither.
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

// §H.12.7: such elements are accessed through pointers, in two steps -- the
// actual address of the element is computed first and then used to access
// the element.
TEST(DpiOtherElementTypes, TheAddressIsComputedFirstAndThenUsed) {
  const std::array<DpiPointerAccessStep, 2> kSteps = DpiPointerAccessSteps();
  EXPECT_EQ(kSteps[0], DpiPointerAccessStep::kComputeTheElementsAddress);
  EXPECT_EQ(kSteps[1], DpiPointerAccessStep::kAccessTheElementThroughIt);
  EXPECT_EQ(DpiElementAccessMethodOf(DataTypeKind::kInt, 0),
            DpiElementAccessMethod::kGenericPointerWithCasting);
}

// The two steps over an open array `int a [2:1][-1:-2]` of C-compatible
// ints laid out as C lays them out: svGetArrElemPtr2 computes the address
// of an element by the actual's own indices, and the element is read and
// written through that address with the int cast the user provides, no
// canonical buffer in between.
TEST(DpiOtherElementTypes, AnIntElementIsReachedThroughItsComputedAddress) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {2, 1}, {-1, -2}};
  int data[2][2] = {{10, 11}, {12, 13}};
  SvOpenArrayDesc desc;
  desc.data = data;
  desc.n_dims = 3;
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
