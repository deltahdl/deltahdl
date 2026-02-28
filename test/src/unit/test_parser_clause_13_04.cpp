// §13.4: Functions

#include "fixture_parser.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// function_body_declaration (old-style ports)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  function int foo;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    foo = a + b;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

// --- Test helpers ---
struct ParseResult14 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult14 Parse(const std::string& src) {
  ParseResult14 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// LRM section 13.4 -- Functions (additional tests)
// =============================================================================
// Function with no ports (implicit return by function name assignment).
TEST(ParserSection13, FunctionNoPorts) {
  auto r = Parse(
      "module m;\n"
      "  function int get_magic();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "get_magic");
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->func_args.empty());
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kInt);
}

// Function with multiple statements in body.
TEST(ParserSection13, FunctionMultipleBodyStmts) {
  auto r = Parse(
      "module m;\n"
      "  function int clamp(int val, int lo, int hi);\n"
      "    if (val < lo) return lo;\n"
      "    if (val > hi) return hi;\n"
      "    return val;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "clamp");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 3u);
  EXPECT_GE(fn->func_body_stmts.size(), 3u);
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
// 23. Automatic function with input/output/inout ports
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncWithAllPortDirs) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void multi_dir(\n"
      "      input int a,\n"
      "      output int b,\n"
      "      inout int c);\n"
      "    b = a + c;\n"
      "    c = a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(item->func_args[2].data_type.kind, DataTypeKind::kInt);
}

}  // namespace
