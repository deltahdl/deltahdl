#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(TypeIncompatibleParsing, StringToInt) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, ChandleToInt) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, EventToInt) {
  DataType a;
  a.kind = DataTypeKind::kEvent;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, StringToChandle) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, ChandleToReal) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, ChandleToEnum) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, ChandleToEvent) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kEvent;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, ChandleToChandleIsCompatible) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(TypeIncompatibleParsing, EventToEventIsCompatible) {
  DataType a;
  a.kind = DataTypeKind::kEvent;
  DataType b;
  b.kind = DataTypeKind::kEvent;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

}  // namespace
