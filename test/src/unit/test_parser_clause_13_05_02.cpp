// §13.5.2: Pass by reference

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA26, FuncBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(const ref int x);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TaskBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TfPortDirectionConstRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

// ---------------------------------------------------------------------------
// tf_port_declaration (old-style): const ref and var
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortDeclOldStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    const ref int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
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
// 16. Automatic function with ref argument
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncWithRefArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void swap(ref int x, ref int y);\n"
      "    int tmp;\n"
      "    tmp = x;\n"
      "    x = y;\n"
      "    y = tmp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_EQ(item->func_args[1].direction, Direction::kRef);
  EXPECT_EQ(item->func_args[1].name, "y");
}

// ---------------------------------------------------------------------------
// tf_port_direction: [ const ] ref [ static ]
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortDirectionRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
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
// LRM section 13.5.2 -- Pass by reference (additional tests)
// =============================================================================
// Automatic function with ref arg (LRM: ref requires automatic lifetime).
TEST(ParserSection13, AutomaticFunctionWithRef) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int crc(ref byte packet[]);\n"
      "    crc = 0;\n"
      "    for (int j = 0; j < 10; j++) begin\n"
      "      crc ^= packet[j];\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "crc");
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kRef);
}

}  // namespace
