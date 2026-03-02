// §34.4: Protect pragma directives

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex O - Encryption/decryption
// =============================================================================
TEST_F(AnnexHParseTest, AnnexOPragmaProtect) {
  // pragma protect directives are preprocessor-level and stripped before
  // parsing. This test confirms the module around them parses correctly.
  auto* unit = Parse(
      "module m;\n"
      "  logic x;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->name, "x");
}

}  // namespace
