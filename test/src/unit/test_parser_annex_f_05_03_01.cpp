// Annex F.5.3.1: Neutral satisfaction

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// Annex F -- Formal semantics of concurrent assertions
// =============================================================================
TEST(ParserAnnexF, AnnexFAssertPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
