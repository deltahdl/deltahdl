// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns the first module item from the first module.
static ModuleItem* FirstItem(ParseResult4d& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

namespace {

// =============================================================================
// 14. Automatic function with multiple local vars of different types
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncMultiTypedLocalVars) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int mixed_locals(int x);\n"
      "    int a;\n"
      "    logic [7:0] b;\n"
      "    real c;\n"
      "    a = x;\n"
      "    b = x;\n"
      "    c = x;\n"
      "    return a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 3u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_body_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[1]->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->func_body_stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[2]->var_decl_type.kind, DataTypeKind::kReal);
}

// =============================================================================
// 15. Automatic function with output argument
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncWithOutputArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void compute(input int a, output int b);\n"
      "    b = a * 3;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

}  // namespace
