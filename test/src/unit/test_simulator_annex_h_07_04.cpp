#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

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

TEST(DpiBasicTypes, EachBasicTypeMapsToItsCType) {
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
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kByte, Direction::kInput, false), false),
            "const char");
}

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
