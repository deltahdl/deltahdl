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

TEST_F(AnnexHParseTest, AnnexGProcessScopeResolution) {
  // process::self() uses scope-resolution syntax at the module-item level.
  // The parser handles pkg::type as a named type with scope prefix.
  auto* unit = Parse(
      "module m;\n"
      "  process::state_e st;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.scope_name, "process");
  EXPECT_EQ(items[0]->data_type.type_name, "state_e");
}

// =============================================================================
// LRM section 9.7 -- Fine-grain process control
// The process class: self(), status(), kill(), await(), suspend(), resume().
// =============================================================================
TEST(ParserSection9c, ProcessSelfAssignment) {
  // process p = process::self(); is valid usage.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9c, ProcessKillCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "    fork\n"
              "      begin\n"
              "        #100;\n"
              "      end\n"
              "    join_none\n"
              "    p.kill();\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// Annex G -- Std package classes (process, semaphore, mailbox)
// =============================================================================
TEST(ParserAnnexG, AnnexGProcessDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
