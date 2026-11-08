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

TEST(DpiTypeDuality, TheDirectionOfTheFormalShapesTheCDefinition) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), false),
      "const int");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), false),
      "int*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInout), false),
      "int*");
}

TEST(DpiTypeDuality, ASmallInputIsPassedByValueAsItsTableType) {
  auto in = [](DataTypeKind k, uint32_t w = 0) {
    return DpiCTypeOfFormal(Formal(k, Direction::kInput, w), false);
  };
  EXPECT_EQ(in(DataTypeKind::kByte), "const char");
  EXPECT_EQ(in(DataTypeKind::kShortint), "const short int");
  EXPECT_EQ(in(DataTypeKind::kLongint), "const long long");
  EXPECT_EQ(in(DataTypeKind::kReal), "const double");
  EXPECT_EQ(in(DataTypeKind::kShortreal), "const float");
  EXPECT_EQ(in(DataTypeKind::kChandle), "const void*");
  EXPECT_EQ(in(DataTypeKind::kString), "const char*");
  EXPECT_EQ(in(DataTypeKind::kBit), "const svBit");
  EXPECT_EQ(in(DataTypeKind::kBit, 1), "const svBit");
  EXPECT_EQ(in(DataTypeKind::kLogic), "const svLogic");
  EXPECT_EQ(in(DataTypeKind::kReg), "const svLogic");
  for (DataTypeKind k :
       {DataTypeKind::kByte, DataTypeKind::kShortint, DataTypeKind::kInt,
        DataTypeKind::kLongint, DataTypeKind::kReal, DataTypeKind::kShortreal,
        DataTypeKind::kBit, DataTypeKind::kLogic, DataTypeKind::kChandle,
        DataTypeKind::kString}) {
    EXPECT_TRUE(DpiTypeIsSmall(k));
  }
  EXPECT_FALSE(DpiTypeIsSmall(DataTypeKind::kInteger));
  EXPECT_FALSE(DpiTypeIsSmall(DataTypeKind::kTime));
  EXPECT_FALSE(DpiTypeIsSmall(DataTypeKind::kStruct));
}

TEST(DpiTypeDuality, APackedArrayIsPassedByReferenceToItsCanonicalForm) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kInput, 8), false),
      "const svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput, 8),
                             false),
            "svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLogic, Direction::kInput, 33), false),
            "const svLogicVecVal*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kReg, Direction::kInout, 4), false),
      "svLogicVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kInteger, Direction::kInput),
                             false),
            "const svLogicVecVal*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kTime, Direction::kOutput), false),
      "svLogicVecVal*");
}

TEST(DpiTypeDuality, AnOpenArrayIsPassedByHandleWhateverItsDirection) {
  for (Direction d :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kBit, d, 8), true),
              "const svOpenArrayHandle");
    EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kInt, d), true),
              "const svOpenArrayHandle");
  }
}

TEST(DpiTypeDuality, AnOutputOfASmallTypeIsAPointerToItsTableType) {
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kString, Direction::kOutput),
                             false),
            "const char**");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kChandle, Direction::kInout),
                             false),
            "void**");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput), false),
      "svBit*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kStruct, Direction::kInput), false),
      "");
}

}  // namespace
