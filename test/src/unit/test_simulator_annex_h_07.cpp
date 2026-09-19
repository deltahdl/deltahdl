#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.7 (Data types) defines the data types of the C layer of the DPI:
// a value crosses the interface as one of them -- a basic type of Table H.1
// (§H.7.4), the canonical representation of a packed array (§H.7.7), or the
// handle of an open array (§H.12) -- and a type none of them covers does not
// cross. The cases check which of the layer's types each formal crosses as
// and which subclause defines it.

namespace {

DpiArg Formal(DataTypeKind type, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = Direction::kInput;
  formal.width = width;
  return formal;
}

// §H.7: an int, a real, a string, a chandle and a scalar bit cross as basic
// types, a bit [63:0], an integer and a time in the canonical representation,
// an open array of anything by handle, and a struct or event not at all.
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

// §H.7: the subclause that defines each of the layer's types -- H.7.4 the
// basic types, H.7.7 the canonical representation, H.12 the open array
// handle -- and none for what does not cross.
TEST(DpiCLayerDataTypes, EachOfTheLayersTypesHasItsDefiningSubclause) {
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kBasic), "H.7.4");
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kCanonicalElement),
            "H.7.7");
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kOpenArrayHandle),
            "H.12");
  EXPECT_EQ(DpiSubclauseDefiningCLayerType(DpiCLayerType::kNone), "");
}

}  // namespace
