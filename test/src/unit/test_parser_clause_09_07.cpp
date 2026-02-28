// §9.7: Fine-grain process control

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex G - Std package: process class (§G.1)
// =============================================================================
TEST_F(AnnexHParseTest, AnnexGProcessMethodCalls) {
  // Process method calls (.status, .kill, etc.) parse as member-access calls.
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    p.status();\n"
      "    p.kill();\n"
      "    p.await();\n"
      "    p.suspend();\n"
      "    p.resume();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

}  // namespace
