// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypesMatchNamedDifferent) {
  // Two named types with different names should not match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesEquivalentSameKind) {
  // §6.22.2: Same kind, same signedness, same state-ness -> equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

}  // namespace
