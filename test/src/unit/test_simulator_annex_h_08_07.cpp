#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg Input(DataTypeKind type, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = Direction::kInput;
  formal.width = width;
  return formal;
}

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

TEST(DpiInputArgumentPassing, AnOpenArrayInputIsTheConstHandle) {
  EXPECT_EQ(DpiPassingModeOfFormal(Input(DataTypeKind::kInt), true),
            DpiPassingMode::kByHandle);
  EXPECT_EQ(DpiCTypeOfFormal(Input(DataTypeKind::kInt), true),
            "const svOpenArrayHandle");
}

}  // namespace
