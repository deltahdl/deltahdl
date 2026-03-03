// §6.22.3: Assignment compatible

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, AssignmentCompatibleRealToReal) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

}  // namespace
