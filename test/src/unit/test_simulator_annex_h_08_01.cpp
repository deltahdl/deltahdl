#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

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
