// Annex D.4: $input

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- D.3: $input ---
TEST(ParserAnnexD2, AnnexDInput) {
  auto r = Parse(
      "module m;\n"
      "  initial $input(\"commands.txt\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

}  // namespace
