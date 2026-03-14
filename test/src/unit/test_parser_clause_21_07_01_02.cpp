#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpvarsNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsWithLevels) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(1, t);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsAllLevels) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, t);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsMultipleScopes) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top.mod1, top.mod2.net1);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsLevelOneModule) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(1, top);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsLevelZeroAllHierarchy) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsMixedModulesAndVars) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top.mod1, top.mod2.net1);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsInsideBeginEnd) {
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
