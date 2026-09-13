#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.8.3 (Argument passing by value): only small values of formal
// input arguments are passed by value, function results are directly
// passed by value as well, and the user provides the C type equivalent to
// the SystemVerilog type of a formal passed by value. The cases check which
// formals are passed by value, the C type the user provides for one, and
// the C type a function result is returned as.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.3: an input of a small type -- int, real, scalar logic, chandle,
// string -- is passed by value; an output of a small type, an input packed
// array and an open array are not.
TEST(DpiPassingByValue, OnlyASmallInputIsPassedByValue) {
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kInput), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kReal, Direction::kInput), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kLogic, Direction::kInput, 1), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kChandle, Direction::kInput), false));
  EXPECT_TRUE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kString, Direction::kInput), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kOutput), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kInout), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kBit, Direction::kInput, 8), false));
  EXPECT_FALSE(DpiFormalIsPassedByValue(
      Formal(DataTypeKind::kInt, Direction::kInput), true));
}

// §H.8.3: the C type the user provides for a formal passed by value is the
// equivalent of its SystemVerilog type, Table H.1's with the const of an
// input -- const int, const double, const svLogic, const char* -- and
// DpiCTypeOfFormal is that type.
TEST(DpiPassingByValue, TheUserProvidesTheEquivalentCType) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), false),
      "const int");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kReal, Direction::kInput), false),
      "const double");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kLogic, Direction::kInput, 1),
                             false),
            "const svLogic");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kString, Direction::kInput), false),
      "const char*");
}

// §H.8.3: a function result is directly passed by value, as the C type of
// its SystemVerilog type without a qualifier -- int, double, svBit, const
// char* for a string, void* for a chandle, void for none -- and a packed
// array or a struct, which §35.5.5 keeps from being a result, has no result
// type.
TEST(DpiPassingByValue, TheResultIsReturnedByValueAsItsCType) {
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kInt), "int");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kReal), "double");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kBit), "svBit");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kString), "const char*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kChandle), "void*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kVoid), "void");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kInteger), "");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kStruct), "");
}

}  // namespace
