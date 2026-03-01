// Annex D.12: $showscopes

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- D.7: $showscopes with argument ---
TEST(ParserAnnexD2, AnnexDShowscopesArg) {
  auto r = Parse(
      "module m;\n"
      "  initial $showscopes(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

}  // namespace
