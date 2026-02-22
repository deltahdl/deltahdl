#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult612 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult612 Parse(const std::string &src) {
  ParseResult612 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FirstItem(ParseResult612 &r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto &items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =============================================================================
// LRM section 6.12 -- Real, shortreal, and realtime data types
// =============================================================================

TEST(ParserSection6, RealDecl) {
  // real is same as C double (LRM 6.12)
  auto r = Parse(
      "module m;\n"
      "  real r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(item->name, "r");
}

TEST(ParserSection6, ShortrealDecl) {
  // shortreal is same as C float (LRM 6.12)
  auto r = Parse(
      "module m;\n"
      "  shortreal sr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_EQ(item->name, "sr");
}

TEST(ParserSection6, RealtimeDecl) {
  // realtime is synonymous with real (LRM 6.12)
  auto r = Parse(
      "module m;\n"
      "  realtime rt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
  EXPECT_EQ(item->name, "rt");
}

TEST(ParserSection6, RealWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  real pi = 3.14159;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, ShortrealWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  shortreal f = 1.5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, MultipleRealDecls) {
  auto r = Parse(
      "module m;\n"
      "  real a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection6, AllRealTypes) {
  // All three real-family types in one module
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  shortreal sr;\n"
              "  realtime rt;\n"
              "endmodule\n"));
}

// --- Real literals (LRM 5.7/5.8, used with §6.12 types) ---

TEST(ParserSection6, RealLiteralDecimalPoint) {
  // Standard decimal point real literal
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.5;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralScientificNotation) {
  // Scientific notation: 1.3e2 = 130.0
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.3e2;\n"
              "endmodule\n"));
}

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
  auto *item = FirstItem(r);
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
