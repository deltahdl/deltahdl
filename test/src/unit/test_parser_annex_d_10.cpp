// Annex D.10: $scale

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- D.6: $scale ---
TEST(ParserAnnexD2, AnnexDScaleParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $scale(hier_ref);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

}  // namespace
