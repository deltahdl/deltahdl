// §13.5.3: Default argument values

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfTfVariableIdentifiersWithDefaults) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a = 1, input int b = 2);\n"
      "    compute = a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->func_args.size(), 2u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
  EXPECT_NE(item->func_args[1].default_value, nullptr);
}

TEST(ParserA26, FuncBodyNewStyleWithDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(input int x = 5);\n"
      "    return x;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(ParserA27, TaskBodyNewStyleDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x = 5);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
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
// 21. Automatic function with default argument values
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncWithDefaultArgs) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int scale(int x, int factor = 2);\n"
      "    return x * factor;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
  EXPECT_EQ(item->func_args[1].name, "factor");
  EXPECT_NE(item->func_args[1].default_value, nullptr);
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
// LRM section 13.5.3 -- Default argument values (additional tests)
// =============================================================================
// Mix of default and non-default args (non-default first, default last).
TEST(ParserSection13, MixedDefaultAndNonDefaultArgs) {
  auto r = Parse(
      "module m;\n"
      "  function int fun(int j, string s = \"no\", int k = 0);\n"
      "    return j;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "fun");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 3u);
  EXPECT_EQ(fn->func_args[0].default_value, nullptr);
  EXPECT_NE(fn->func_args[1].default_value, nullptr);
  EXPECT_NE(fn->func_args[2].default_value, nullptr);
}

// Default arg with expression (not just literal).
TEST(ParserSection13, DefaultArgWithExpression) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(int size = 8 * 4);\n"
      "    return size;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "compute");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  ASSERT_NE(fn->func_args[0].default_value, nullptr);
  EXPECT_EQ(fn->func_args[0].default_value->kind, ExprKind::kBinary);
}

static ModuleItem* FindFunc(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl) {
      continue;
    }
    if (item->name == name) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 13.5.3 -- Default argument values
// =============================================================================
TEST(ParserSection13, DefaultArgValues) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a = 0, int b = 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_NE(fn->func_args[0].default_value, nullptr);
  EXPECT_NE(fn->func_args[1].default_value, nullptr);
}

TEST(ParserSection13, DefaultArgValueOnTask) {
  auto r = Parse(
      "module m;\n"
      "  task bar(int x, int y = 10);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "bar");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].default_value, nullptr);
  EXPECT_NE(tk->func_args[1].default_value, nullptr);
}

}  // namespace
