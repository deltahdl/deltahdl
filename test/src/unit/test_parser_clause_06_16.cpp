#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FirstItem(ParseResult616& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =============================================================================
// LRM section 6.16 -- String data type
// =============================================================================

TEST(ParserSection6, StringDeclBasic) {
  // string variable declaration (LRM 6.16)
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_EQ(item->name, "s");
}

TEST(ParserSection6, StringDeclWithInitializer) {
  // string variable with initial value
  auto r = Parse(
      "module m;\n"
      "  string name = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, StringDeclEmptyInit) {
  // string initialized to empty string
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string s = \"\";\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringParameterDecl) {
  // parameter string (LRM 6.16)
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter string DEFAULT_NAME = \"John Smith\";\n"
              "  string myName = DEFAULT_NAME;\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringInFunctionArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void greet(string name);\n"
              "    $display(\"Hello %s\", name);\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringFunctionReturn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function string get_msg();\n"
              "    return \"ok\";\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringConcatOp) {
  // String concatenation using {} operator
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string a, b, c;\n"
              "  initial begin\n"
              "    a = \"hello\";\n"
              "    b = \" world\";\n"
              "    c = {a, b};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringComparison) {
  // String comparison operators
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string a, b;\n"
              "  initial begin\n"
              "    a = \"abc\";\n"
              "    b = \"def\";\n"
              "    if (a == b) $display(\"equal\");\n"
              "    if (a != b) $display(\"not equal\");\n"
              "    if (a < b) $display(\"less\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, MultipleStringDecls) {
  auto r = Parse(
      "module m;\n"
      "  string x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}
