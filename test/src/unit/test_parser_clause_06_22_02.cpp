// §6.22.2: Equivalent types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypesNotEquivalentDifferentSign) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

}  // namespace
