#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.8.7 (Input arguments): an input argument of an imported function
// implemented in C shall always have a const qualifier; an input, open
// arrays apart, is passed by value or by reference depending on its size,
// a small value by value, and the small types are byte, shortint, int,
// longint, real and shortreal, scalar bit and logic, and chandle and
// string, an input of any other type being passed by reference. The cases
// check the list of small types, that each is passed by value under const
// and every other input by reference under const, and that an open array
// input is the const handle.

namespace {

DpiArg Input(DataTypeKind type, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = Direction::kInput;
  formal.width = width;
  return formal;
}

// §H.8.7: the ten small types, in the clause's order, and each is small.
TEST(DpiInputArgumentPassing, TheSmallTypesAreTheTenTheClauseLists) {
  const std::vector<DataTypeKind> kExpected = {
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kReal,     DataTypeKind::kShortreal,
      DataTypeKind::kBit,     DataTypeKind::kLogic,    DataTypeKind::kChandle,
      DataTypeKind::kString};
  EXPECT_EQ(DpiSmallTypes(), kExpected);
  for (const DataTypeKind kKind : DpiSmallTypes()) {
    EXPECT_TRUE(DpiTypeIsSmall(kKind));
  }
  EXPECT_FALSE(DpiTypeIsSmall(DataTypeKind::kInteger));
  EXPECT_FALSE(DpiTypeIsSmall(DataTypeKind::kTime));
  EXPECT_FALSE(DpiTypeIsSmall(DataTypeKind::kStruct));
}

// §H.8.7: an input of each small type is passed by value with const, and
// an input of another type -- integer, time, a packed bit or logic array
// -- by reference with const.
TEST(DpiInputArgumentPassing, ASmallInputByValueAndAnyOtherByReference) {
  for (const DataTypeKind kKind : DpiSmallTypes()) {
    const DpiArg kFormal = Input(kKind, 1);
    EXPECT_EQ(DpiPassingModeOfFormal(kFormal, false), DpiPassingMode::kByValue);
    const std::string kType = DpiCTypeOfFormal(kFormal, false);
    EXPECT_TRUE(kType.starts_with("const ")) << kType;
  }
  for (const DpiArg& formal :
       {Input(DataTypeKind::kInteger), Input(DataTypeKind::kTime),
        Input(DataTypeKind::kBit, 8), Input(DataTypeKind::kLogic, 64)}) {
    EXPECT_EQ(DpiPassingModeOfFormal(formal, false),
              DpiPassingMode::kByReference);
    const std::string kType = DpiCTypeOfFormal(formal, false);
    EXPECT_TRUE(kType.starts_with("const ")) << kType;
    EXPECT_TRUE(kType.ends_with("*")) << kType;
  }
}

// §H.8.7: an open array input is the exception to value or reference,
// passed by handle, and const like every input.
TEST(DpiInputArgumentPassing, AnOpenArrayInputIsTheConstHandle) {
  EXPECT_EQ(DpiPassingModeOfFormal(Input(DataTypeKind::kInt), true),
            DpiPassingMode::kByHandle);
  EXPECT_EQ(DpiCTypeOfFormal(Input(DataTypeKind::kInt), true),
            "const svOpenArrayHandle");
}

}  // namespace
