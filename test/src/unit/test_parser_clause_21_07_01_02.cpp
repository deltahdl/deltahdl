// §21.7.1.2: Specifying variables to be dumped ($dumpvars)

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpvarsNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars;\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsWithLevels) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(1, t);\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsAllLevels) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, t);\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsMultipleScopes) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top.mod1, top.mod2.net1);\n"
              "endmodule\n"));
}

// ============================================================================
// LRM section 21.7.1.2 -- Specifying variables to be dumped ($dumpvars)
// ============================================================================
TEST(ParserSection21, DumpvarsLevelOneModule) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(1, top);\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsLevelZeroAllHierarchy) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top);\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsMixedModulesAndVars) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top.mod1, top.mod2.net1);\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsInsideBeginEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $dumpfile(\"test.vcd\");\n"
      "    $dumpvars(0, t);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

}  // namespace
