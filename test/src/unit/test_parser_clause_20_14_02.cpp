// §20.14.2: Distribution functions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// Annex N -- Probabilistic distribution functions
// =============================================================================
TEST(ParserAnnexN, AnnexNDistUniform) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_uniform(seed, 0, 100);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

}  // namespace
