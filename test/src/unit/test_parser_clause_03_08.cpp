// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, TaskWithAllArgDirections) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  task xfer(input int a, output int b, inout int c, ref int d);\n"
      "    b = a;\n"
      "    c = c + 1;\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, TaskCalledAsStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task greet; endtask\n"
              "  initial greet();\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, FunctionWithReturnValue) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
}

TEST(DesignBuildingBlockParsing, VoidFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void log(int val);\n"
              "    $display(\"%0d\", val);\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, NonVoidFunctionUsedAsOperand) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int twice(int v); return v * 2; endfunction\n"
              "  logic [31:0] result;\n"
              "  initial result = twice(5);\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, VoidFunctionCalledAsStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void log(int v); $display(\"%0d\", v); endfunction\n"
              "  initial log(42);\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, FunctionWithAllArgDirections) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int compute(input int a, output int b,\n"
              "                       inout int c, ref int d);\n"
              "    b = a;\n"
              "    c = c + 1;\n"
              "    return a + d;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, TaskAndFunctionCoexist) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  task do_nothing; endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTaskDecl));
}

}  // namespace
