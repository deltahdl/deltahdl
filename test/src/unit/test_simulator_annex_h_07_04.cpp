#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.7.4 (Basic types): Table H.1 maps the basic SystemVerilog data
// types to C types, the DPI supports the unsigned integer types with the
// unsigned C types corresponding to the table's signed ones, and an input of
// byte unsigned or shortint unsigned is not equivalent to a bit [7:0] or
// bit [15:0], the former being passed by value as unsigned char and
// unsigned short and the latter by reference as svBitVecVal, nor is the
// pair equivalent under output or inout, where the one is an unsigned char*
// and the other an svBitVecVal*. The cases check each row of the table, the
// four unsigned types, and the pair of passings under each direction.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, bool is_unsigned,
              uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.is_unsigned = is_unsigned;
  formal.width = width;
  return formal;
}

// Table H.1: byte is char, shortint short int, int int, longint long long,
// real double, shortreal float, chandle void*, string const char*, and bit
// and logic -- reg using logic's encoding -- unsigned char, the encodings
// being svdpi.h's; a type the table has no row for maps to nothing.
TEST(DpiBasicTypes, TableH1MapsEachBasicTypeToItsCType) {
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kByte, false), "char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kShortint, false), "short int");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kInt, false), "int");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kLongint, false), "long long");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kReal, false), "double");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kShortreal, false), "float");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kChandle, false), "void*");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kString, false), "const char*");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kBit, false), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kLogic, false), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kReg, false), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kStruct, false), "");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kEvent, false), "");
}

// §H.7.4: the unsigned integer types map to the unsigned C types
// corresponding to the table's rows for their signed equivalents; a type
// with no signed row is unaffected by the qualifier.
TEST(DpiBasicTypes, TheUnsignedIntegerTypesMapToTheUnsignedCTypes) {
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kByte, true), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kShortint, true),
            "unsigned short");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kInt, true), "unsigned int");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kLongint, true),
            "unsigned long long");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kReal, true), "double");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kBit, true), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kString, true), "const char*");
}

// §H.7.4: an input of byte unsigned is passed by value as unsigned char and
// one of shortint unsigned as unsigned short, where bit [7:0] and bit [15:0]
// are passed by reference as svBitVecVal, so neither pair is equivalent.
TEST(DpiBasicTypes, AnUnsignedByteInputIsNotABitVectorOfEight) {
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kByte, Direction::kInput, true), false),
            "const unsigned char");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kBit, Direction::kInput, false, 8), false),
            "const svBitVecVal*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kShortint, Direction::kInput, true),
                       false),
      "const unsigned short");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kInput, false, 16),
                       false),
      "const svBitVecVal*");
  // The signed types keep the table's rows.
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kByte, Direction::kInput, false), false),
            "const char");
}

// §H.7.4: the same lack of equivalence holds under output and inout, where
// byte unsigned is an unsigned char* and bit [7:0] an svBitVecVal*.
TEST(DpiBasicTypes, AnUnsignedByteOutputIsNotABitVectorOfEight) {
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kByte, Direction::kOutput, true), false),
            "unsigned char*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput, false, 8),
                       false),
      "svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLongint, Direction::kInout, true), false),
            "unsigned long long*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kInout, true), false),
            "unsigned int*");
}

}  // namespace
