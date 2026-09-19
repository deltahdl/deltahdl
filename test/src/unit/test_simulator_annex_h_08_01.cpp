#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.8.1 (Overview): imported and exported function arguments are
// generally passed by some form of reference, with the exception of small
// values of input arguments, which are passed by value; the function
// result, restricted to small values, is likewise passed by value, directly
// returned; a formal other than an open array is passed by direct reference
// or by value and is therefore directly accessible in C, and an open array
// formal is passed by a handle and reached through library functions. The
// cases check that reference and handle are the forms of reference and
// value the exception a small input alone takes, and that a result is
// restricted to the small values and returned by value.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.1: by reference and by handle are forms of reference and by value
// is not; a small input is the exception passed by value, and the same
// small type as an output or inout goes back to a form of reference, as
// does an input that is not small.
TEST(DpiPassingOverview, ArgumentsAreGenerallyPassedBySomeFormOfReference) {
  EXPECT_TRUE(DpiModeIsAFormOfReference(DpiPassingMode::kByReference));
  EXPECT_TRUE(DpiModeIsAFormOfReference(DpiPassingMode::kByHandle));
  EXPECT_FALSE(DpiModeIsAFormOfReference(DpiPassingMode::kByValue));
  for (const DataTypeKind kKind : DpiSmallTypes()) {
    EXPECT_EQ(
        DpiPassingModeOfFormal(Formal(kKind, Direction::kInput, 1), false),
        DpiPassingMode::kByValue);
    EXPECT_TRUE(DpiModeIsAFormOfReference(
        DpiPassingModeOfFormal(Formal(kKind, Direction::kOutput, 1), false)));
    EXPECT_TRUE(DpiModeIsAFormOfReference(
        DpiPassingModeOfFormal(Formal(kKind, Direction::kInout, 1), false)));
  }
  EXPECT_TRUE(DpiModeIsAFormOfReference(DpiPassingModeOfFormal(
      Formal(DataTypeKind::kLogic, Direction::kInput, 16), false)));
  EXPECT_TRUE(DpiModeIsAFormOfReference(DpiPassingModeOfFormal(
      Formal(DataTypeKind::kInt, Direction::kInput), true)));
}

// §H.8.1: the function result is restricted to small values -- and void
// for a function returning none -- and passed by value, so a type that may
// be a result has a C type to be returned as and one that may not has none.
TEST(DpiPassingOverview, TheResultIsRestrictedToSmallValuesAndReturnedByValue) {
  EXPECT_EQ(DpiPassingModeOfResult(), DpiPassingMode::kByValue);
  for (const DataTypeKind kKind : DpiSmallTypes()) {
    EXPECT_TRUE(DpiTypeMayBeAResult(kKind));
    EXPECT_FALSE(DpiCTypeOfResult(kKind).empty());
  }
  EXPECT_TRUE(DpiTypeMayBeAResult(DataTypeKind::kVoid));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kInteger));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kTime));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kStruct));
  EXPECT_TRUE(DpiCTypeOfResult(DataTypeKind::kStruct).empty());
}

}  // namespace
