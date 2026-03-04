#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserClause03, Cl3_13_AttributeNameSpace) {
  auto r = Parse(
      "module m;\n"
      "  (* synthesis *) logic flag;\n"
      "  (* full_case, parallel_case *) logic [1:0] sel;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "synthesis"));
  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "full_case"));
}

TEST(ParserClause03, Cl3_13_FunctionWithLocalVarsSubscope) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int compute(int a, int b);\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* func = mod->items[0];
  EXPECT_EQ(func->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(func->name, "compute");

  EXPECT_FALSE(func->func_body_stmts.empty());
}

TEST(ParserClause03, Cl3_13_VarNameSameAsModuleName) {

  EXPECT_TRUE(
      ParseOk("module top;\n"
              "  logic top;\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_13_ForkJoinBlockSubscope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    fork\n"
              "      $display(\"a\");\n"
              "      $display(\"b\");\n"
              "    join\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_13_TextMacroNameSpace) {

  auto r = Parse(
      "`define WIDTH 8\n"
      "`define DEPTH 16\n"
      "module m;\n"
      "  logic [`WIDTH-1:0] data;\n"
      "  logic [`DEPTH-1:0] addr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  EXPECT_TRUE(
      ParseOk("`define data 42\n"
              "module m; logic [7:0] data; endmodule\n"));
}

TEST(ParserClause03, Cl3_13_NestedClassInModule) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class inner_cls;\n"
              "    int value;\n"
              "    function void set(int v);\n"
              "      value = v;\n"
              "    endfunction\n"
              "  endclass\n"
              "endmodule\n"));
}

}
