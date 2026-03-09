#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypeIncompatibleStringInt) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(ParserSection6, TypeIncompatibleChandleInt) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(ParserSection6, TypeIncompatibleEventInt) {
  DataType a;
  a.kind = DataTypeKind::kEvent;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(ParserSection6, TypeIncompatibleStringChandle) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

}
