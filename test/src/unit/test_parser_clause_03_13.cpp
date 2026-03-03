// §3.13: Name spaces

#include "fixture_parser.h"

using namespace delta;

struct ParseResult616 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult616 Parse(const std::string& src) {
  ParseResult616 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// 32. Attribute name space (h) — enclosed by (* and *)
TEST(ParserClause03, Cl3_13_AttributeNameSpace) {
  auto r = Parse(
      "module m;\n"
      "  (* synthesis *) logic flag;\n"
      "  (* full_case, parallel_case *) logic [1:0] sel;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Verify attributes are parsed and attached to declarations
  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "synthesis"));
  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "full_case"));
}

// 29. Function with local variables creating subscope
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
  // The function should have body statements (local var + assign + return).
  EXPECT_FALSE(func->func_body_stmts.empty());
}

// 7. Variable name same as module name (different name spaces)
TEST(ParserClause03, Cl3_13_VarNameSameAsModuleName) {
  // A variable named 'top' inside module 'top' is legal because
  // the definition name space and the local scope are distinct.
  EXPECT_TRUE(
      ParseOk("module top;\n"
              "  logic top;\n"
              "endmodule\n"));
}

// 5. Fork-join block creating a subscope
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

// 31. Text macro name space (d) — `define introduces names with leading `
TEST(ParserClause03, Cl3_13_TextMacroNameSpace) {
  // Macro defined and used; subsequent redefinition overrides previous
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
  // Macro names are unambiguous with other name spaces (leading ` character)
  EXPECT_TRUE(
      ParseOk("`define data 42\n"
              "module m; logic [7:0] data; endmodule\n"));
}

// 30. Nested class (class within a module -- class in module scope)
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

}  // namespace
