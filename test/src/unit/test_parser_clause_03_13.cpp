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
  auto r = ParseWithPreprocessor(
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
      ParseWithPreprocessorOk("`define data 42\n"
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

// §3.13(f): Block name space — named blocks create subscopes.
TEST(ParserClause03, Cl3_13_NamedBlockSubscope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk1\n"
      "    int x;\n"
      "    x = 1;\n"
      "  end\n"
      "  initial begin : blk2\n"
      "    int x;\n"
      "    x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §3.13(g): Port name space — ports overlap module name space.
TEST(ParserClause03, Cl3_13_PortOverlapsModuleScope) {
  EXPECT_TRUE(
      ParseOk("module m (input logic data);\n"
              "endmodule\n"));
}

// §3.13(h): Attribute names are independent of other name spaces.
TEST(ParserClause03, Cl3_13_AttributeNameSameAsVar) {
  auto r = Parse(
      "module m;\n"
      "  (* flag *) logic flag;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §3.13(c): Compilation-unit scope items.
TEST(ParserClause03, Cl3_13_CuScopeFunction) {
  auto r = ParseWithPreprocessor(
      "function automatic int helper(int x); return x + 1; endfunction\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
}

// §3.13(d): Text macro redefinition overrides previous.
TEST(ParserClause03, Cl3_13_MacroRedefinition) {
  auto r = ParseWithPreprocessor(
      "`define VAL 1\n"
      "`define VAL 2\n"
      "module m;\n"
      "  logic [`VAL:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
