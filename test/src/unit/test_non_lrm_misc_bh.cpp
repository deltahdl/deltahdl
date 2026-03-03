// Non-LRM tests

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

static ModuleItem* FirstItem(ParseResult616& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

TEST(ParserSection6, RealLiteralNegativeExponent) {
  // Negative exponent: 1.0e-3 = 0.001
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.0e-3;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralPositiveExponent) {
  // Explicit positive exponent
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 2.5E+4;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralUnderscoresInValue) {
  // Underscores in real literals for readability
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1_000.000_1;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralZeroPointSomething) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 0.123;\n"
              "endmodule\n"));
}

// --- Real conversions (LRM 6.12.1) ---
TEST(ParserSection6, RealToIntAssignment) {
  // Implicit conversion from real to integer (rounds, not truncates)
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  int i;\n"
              "  initial begin\n"
              "    r = 35.7;\n"
              "    i = r;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, IntToRealAssignment) {
  // Implicit conversion from integer to real
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  int i;\n"
              "  initial begin\n"
              "    i = 42;\n"
              "    r = i;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealCastExplicit) {
  // Explicit cast: int'(real_val) (LRM 6.24)
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 3.7;\n"
              "  int i;\n"
              "  initial i = int'(r);\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealInExpression) {
  // Real values in arithmetic expressions
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real a, b, c;\n"
              "  initial begin\n"
              "    a = 1.5;\n"
              "    b = 2.5;\n"
              "    c = a + b;\n"
              "  end\n"
              "endmodule\n"));
}

// --- Shortreal specifics (LRM 6.12) ---
TEST(ParserSection6, ShortrealInModule) {
  // shortreal is same as C float (LRM 6.12)
  auto r = Parse(
      "module m;\n"
      "  shortreal x = 1.0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
}

TEST(ParserSection6, ShortrealInFunctionArg) {
  // shortreal as function argument type
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function shortreal scale(shortreal val, shortreal factor);\n"
              "    return val * factor;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ParserSection6, ShortrealCast) {
  // Cast to shortreal
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int i = 42;\n"
              "  shortreal sr;\n"
              "  initial sr = shortreal'(i);\n"
              "endmodule\n"));
}

TEST(ParserSection6, ShortrealInPort) {
  // shortreal as port type (LRM 23.2.2)
  EXPECT_TRUE(
      ParseOk("module m (input var shortreal in_val,\n"
              "          output var shortreal out_val);\n"
              "  assign out_val = in_val;\n"
              "endmodule\n"));
}

// --- non_integer_type ---
// shortreal | real | realtime
TEST(ParserA221, NonIntegerTypes) {
  auto r = Parse(
      "module m;\n"
      "  shortreal a;\n"
      "  real b;\n"
      "  realtime c;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind,
            DataTypeKind::kShortreal);
  EXPECT_EQ(r.cu->modules[0]->items[1]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(r.cu->modules[0]->items[2]->data_type.kind,
            DataTypeKind::kRealtime);
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

}  // namespace
