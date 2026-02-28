// Annex D.9: $save, $restart, and $incsave

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexD, AnnexDSave) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $save(\"s.sav\"); $restart(\"s.sav\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// --- D.2: $incsave ---
TEST(ParserAnnexD2, AnnexDIncsaveParse) {
  auto r = Parse(
      "module m;\n"
      "  initial $incsave(\"incremental.sav\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

}  // namespace
