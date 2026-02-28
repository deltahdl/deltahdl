// Annex D.3: $getpattern

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// Annex D -- Optional system tasks and system functions
// =============================================================================
// --- D.1: $getpattern ---
TEST(ParserAnnexD2, AnnexDGetpatternParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $getpattern(mem_addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexD2, AnnexDGetpatternRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $getpattern(mem_addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

}  // namespace
