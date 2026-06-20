#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CastCompatibleParsing, RealToShortrealCompatible) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, LogicToEnumCastCompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

}  // namespace
