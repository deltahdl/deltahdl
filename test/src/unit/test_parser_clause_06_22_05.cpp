#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// §6.22.5: String and int are type incompatible (not cast compatible).
TEST(ParserSection6, TypeIncompatibleStringInt) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

// §6.22.5: Chandle and int are type incompatible.
TEST(ParserSection6, TypeIncompatibleChandleInt) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

// §6.22.5: Event and int are type incompatible.
TEST(ParserSection6, TypeIncompatibleEventInt) {
  DataType a;
  a.kind = DataTypeKind::kEvent;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

// §6.22.5: String and chandle are type incompatible.
TEST(ParserSection6, TypeIncompatibleStringChandle) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

}  // namespace
