#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg Formal(DataTypeKind type, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = Direction::kInput;
  formal.width = width;
  return formal;
}

TEST(DpiCLayerDataTypes, EachFormalCrossesAsOneOfTheLayersTypes) {
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kInt), false),
            DpiCLayerType::kBasic);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kReal), false),
            DpiCLayerType::kBasic);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kString), false),
            DpiCLayerType::kBasic);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kChandle), false),
            DpiCLayerType::kBasic);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kBit, 1), false),
            DpiCLayerType::kBasic);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kBit, 64), false),
            DpiCLayerType::kCanonicalElement);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kInteger), false),
            DpiCLayerType::kCanonicalElement);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kTime), false),
            DpiCLayerType::kCanonicalElement);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kBit, 64), true),
            DpiCLayerType::kOpenArrayHandle);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kInt), true),
            DpiCLayerType::kOpenArrayHandle);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kStruct), false),
            DpiCLayerType::kNone);
  EXPECT_EQ(DpiCLayerTypeOfFormal(Formal(DataTypeKind::kEvent), false),
            DpiCLayerType::kNone);
}

TEST(DpiCLayerDataTypes, EachOfTheLayersTypesHasItsDefiningSubclause) {
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kBasic), "H.7.4");
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kCanonicalElement),
            "H.7.7");
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kOpenArrayHandle),
            "H.12");
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kNone), "");
}

}  // namespace
