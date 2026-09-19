#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.7.2 (Duality of types): a value crossing the DPI is of a
// SystemVerilog type on one side and of a C type on the other, so each type
// passed through the interface needs two matching definitions, and the user
// shall provide, for each SystemVerilog type an import or export declaration
// uses, the equivalent C type definition reflecting the argument passing mode
// for the type and the direction of the formal. The cases check the C
// definition matching a formal: that the same SystemVerilog type takes a
// different C definition under each direction, that the passing mode of
// §H.8 -- by value for a small input, by reference otherwise, by handle for
// an open array -- is what decides it, and that the small types are the ones
// §H.8.7 lists.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.7.2: one SystemVerilog type, three directions, three C definitions --
// an input int is passed by value as a const int, an output and an inout by
// reference as an int*.
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

// §H.7.2 with Table H.1 and §H.8.7: each small type is passed by value as
// the C type the table maps it to, with the const qualifier every input
// carries, which a string's const char* carries already.
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

// §H.7.2 with §H.8.4 and §H.8.8: a packed array is passed by reference to its
// canonical representation, a const svBitVecVal* or const svLogicVecVal* for
// an input and the pointer without const for an output or inout; integer and
// time, being packed 4-state types, cross as svLogicVecVal.
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

// §H.7.2 with §H.8.6: an open array is passed by handle whatever its
// direction and type, and the handle carries the const qualifier.
TEST(DpiTypeDuality, AnOpenArrayIsPassedByHandleWhateverItsDirection) {
  for (Direction d :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kBit, d, 8), true),
              "const svOpenArrayHandle");
    EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kInt, d), true),
              "const svOpenArrayHandle");
  }
}

// §H.7.2: an output of a small type is passed by reference as a pointer to
// its table type -- a string as a const char**, a chandle as a void**.
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
