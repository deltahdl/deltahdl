#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpvarsNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpvarsWithLevelAndScope) {
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

// The module/variable list is optional, so a level count with no scope list
// is still a well-formed call.
TEST(IoSystemTaskParsing, DumpvarsLevelsWithoutScopeList) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0);\n"
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
