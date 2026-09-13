#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.8 (Argument passing modes) defines the ways to pass arguments in
// the C layer of the DPI, and §H.8.1 gives the overview: an argument is
// generally passed by some form of reference, except a small value of an
// input argument, which is passed by value, and the function result, which
// being restricted to small values is passed by value, directly returned;
// a formal other than an open array is passed by direct reference or by
// value and so is directly accessible in C, and an open array formal is
// passed by handle and reached through library functions. The cases check
// which mode each formal takes and how the mode shows in the C type.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8: a small input is passed by value, a small output or inout and any
// packed array by reference, and an open array by handle whatever its type
// or direction.
TEST(DpiArgumentPassingModes, EachFormalIsPassedInOneOfThreeModes) {
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kInput), false),
            DpiPassingMode::kByValue);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kString, Direction::kInput), false),
            DpiPassingMode::kByValue);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kOutput), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kInout), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kBit, Direction::kInput, 8), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInteger, Direction::kInput), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kBit, Direction::kInput, 8), true),
            DpiPassingMode::kByHandle);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kOutput), true),
            DpiPassingMode::kByHandle);
}

// §H.8: the mode is what the C type shows -- a value's type as it is, a
// reference as a pointer to it, a handle as svOpenArrayHandle -- and a
// formal passed by value or by reference is directly accessible in C where
// one passed by handle is reached through the library functions.
TEST(DpiArgumentPassingModes, TheModeShowsInTheCType) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), false),
      "const int");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), false),
      "int*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), true),
      "const svOpenArrayHandle");
  EXPECT_TRUE(DpiFormalIsDirectlyAccessibleInC(DpiPassingMode::kByValue));
  EXPECT_TRUE(DpiFormalIsDirectlyAccessibleInC(DpiPassingMode::kByReference));
  EXPECT_FALSE(DpiFormalIsDirectlyAccessibleInC(DpiPassingMode::kByHandle));
}

// §H.8.1: the function result, restricted to small values, is passed by
// value, directly returned.
TEST(DpiArgumentPassingModes, TheResultIsPassedByValue) {
  EXPECT_EQ(DpiPassingModeOfResult(), DpiPassingMode::kByValue);
}

}  // namespace
