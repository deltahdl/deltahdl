#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.7.8 (Unpacked aggregate arguments): imported and exported DPI
// subroutines can take unpacked aggregate types -- unpacked arrays and
// structures -- as formal or actual arguments, composed of packed elements,
// unpacked elements or both, subaggregates included, the nonaggregate
// elements being the basic types of Table H.1 (§35.5.6); and where an
// unpacked type consists purely of unpacked elements, subaggregates
// included, the layout presented to the C programmer is guaranteed to be
// compatible with the C compiler's layout on the operating system, an
// aggregate with packed elements being possible without that guarantee.
// The cases check which aggregates the interface takes and which of them
// have the guaranteed layout.

namespace {

DpiAggregateElement Basic(DataTypeKind kind, uint32_t width = 0) {
  DpiAggregateElement element;
  element.kind = kind;
  element.width = width;
  return element;
}

DpiAggregateElement Struct(std::vector<DpiAggregateElement> members) {
  DpiAggregateElement element;
  element.kind = DataTypeKind::kStruct;
  element.members = std::move(members);
  return element;
}

// §H.7.8: an aggregate of basic types is an argument the interface takes,
// as is one of packed elements, one with a subaggregate, and one with both
// kinds of element; one holding an event, which Table H.1 has no row for,
// is not.
TEST(DpiUnpackedAggregates, AnAggregateOfLegalElementsIsAnArgument) {
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kReal)})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kBit, 8), Basic(DataTypeKind::kLogic, 32)})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kChandle)})})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kByte), Basic(DataTypeKind::kBit, 16)})));
  EXPECT_FALSE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kEvent)})));
  EXPECT_FALSE(DpiAggregateIsAnArgument(
      Struct({Struct({Basic(DataTypeKind::kEvent)})})));
}

// §H.7.8: the layout is guaranteed C compatible where every element, down
// through the subaggregates, is unpacked -- an int, a real, a scalar bit,
// a chandle -- and not where a packed element, a bit [7:0] or an integer,
// lies anywhere in it.
TEST(DpiUnpackedAggregates, PurelyUnpackedElementsHaveTheCCompilersLayout) {
  EXPECT_TRUE(DpiAggregateLayoutIsCCompatible(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kReal),
              Basic(DataTypeKind::kBit, 1), Basic(DataTypeKind::kChandle)})));
  EXPECT_TRUE(DpiAggregateLayoutIsCCompatible(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kLongint)})})));
  EXPECT_FALSE(DpiAggregateLayoutIsCCompatible(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kBit, 8)})));
  EXPECT_FALSE(DpiAggregateLayoutIsCCompatible(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kInteger)})})));
}

}  // namespace
