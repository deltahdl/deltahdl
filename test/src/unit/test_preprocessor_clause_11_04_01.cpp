// §11.4.1: Assignment operators

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// LRM section 10.8 -- Operator assignments (+=, -=, etc.)
// =============================================================================
TEST(ParserSection10, OperatorAssignPlusEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a += 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

}  // namespace
