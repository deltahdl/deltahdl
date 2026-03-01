// §10.6.1: The assign and deassign procedural statements

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// LRM section 10.6.1 -- Procedural assign / deassign
// =============================================================================
TEST(ParserSection10, ProceduralAssignKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, ProceduralAssignLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
}

}  // namespace
