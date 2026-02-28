// §13.4.1: Return values and void functions

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- data_type_or_void ---
// data_type | void
TEST(ParserA221, DataTypeOrVoidReturn) {
  // void as function return type (data_type_or_void)
  auto r = Parse(
      "module m;\n"
      "  function void do_nothing; endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

// =============================================================================
// A.2.6 Function declarations
// =============================================================================
// ---------------------------------------------------------------------------
// function_data_type_or_implicit ::=
//   data_type_or_void | implicit_data_type
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncReturnTypeExplicitInt) {
  auto r = Parse(
      "module m;\n  function int foo(); return 0; endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(ParserA26, FuncReturnTypeVoid) {
  auto r = Parse("module m;\n  function void bar(); endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserA26, FuncReturnTypeLogicPacked) {
  auto r = Parse(
      "module m;\n  function logic [3:0] baz();\n"
      "    return 4'b0;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

// §3.8: Function returning value, void function, all 4 argument directions.
TEST(ParserClause03, Cl3_8_FunctionReturnAndVoidAndDirections) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a, output int b,\n"
      "                       inout int c, ref int d);\n"
      "    b = a;\n"
      "    return a + c + d;\n"
      "  endfunction\n"
      "  function void show(input int val);\n"
      "    $display(\"%d\", val);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl),
      2);
  const auto* compute = FindFunctionByName(r.cu->modules[0]->items, "compute");
  ASSERT_NE(compute, nullptr);
  ASSERT_EQ(compute->func_args.size(), 4u);
  EXPECT_EQ(compute->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(compute->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(compute->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(compute->func_args[3].direction, Direction::kRef);
}

struct ParseResult4e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4e Parse(const std::string& src) {
  ParseResult4e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// 17. Automatic function returning void
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncReturningVoid) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void log_msg(input int code);\n"
      "    $display(\"code=%0d\", code);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
  EXPECT_EQ(item->name, "log_msg");
}

}  // namespace
