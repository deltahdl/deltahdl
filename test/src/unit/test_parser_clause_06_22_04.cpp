// §6.22.4: Cast compatible

#include "fixture_parser.h"
#include "elaborator/type_eval.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =========================================================================
// §6.22: Cast compatibility
// =========================================================================
TEST(ParserSection6, CastCompatibleRealToIntType) {
  // §6.22.4: real and int are cast compatible.
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

}  // namespace
