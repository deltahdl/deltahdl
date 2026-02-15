#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult4 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4 Parse(const std::string& src) {
  ParseResult4 result;
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

static ModuleItem* FirstItem(ParseResult4& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =============================================================================
// LRM section 6.11 -- Integer data types (§4.1 Integers)
// =============================================================================

// --- 2-state integer types ---

TEST(ParserSection4, IntegerTypeByteDecl) {
  auto r = Parse(
      "module m;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->name, "b");
}

TEST(ParserSection4, IntegerTypeShortintDecl) {
  auto r = Parse(
      "module m;\n"
      "  shortint si;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(item->name, "si");
}

TEST(ParserSection4, IntegerTypeIntDecl) {
  auto r = Parse(
      "module m;\n"
      "  int i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "i");
}

TEST(ParserSection4, IntegerTypeLongintDecl) {
  auto r = Parse(
      "module m;\n"
      "  longint li;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->name, "li");
}

// --- 4-state integer types ---

TEST(ParserSection4, IntegerTypeIntegerDecl) {
  // 'integer' is 4-state, 32-bit signed (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  integer x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(item->name, "x");
}

TEST(ParserSection4, IntegerTypeLogicDecl) {
  // 'logic' is 4-state, user-defined width, unsigned (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserSection4, IntegerTypeRegDecl) {
  // 'reg' is identical to 'logic' (LRM 6.11.2)
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(item->name, "r");
}

TEST(ParserSection4, IntegerTypeBitDecl) {
  // 'bit' is 2-state, user-defined width, unsigned (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  bit [31:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(item->name, "val");
}

TEST(ParserSection4, IntegerTypeTimeDecl) {
  // 'time' is 4-state, 64-bit unsigned (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  time t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_EQ(item->name, "t");
}

// --- Signed and unsigned qualifiers (LRM 6.11.3) ---

TEST(ParserSection4, IntUnsignedDecl) {
  // int unsigned -- explicit unsigned override (LRM 6.11.3)
  auto r = Parse(
      "module m;\n"
      "  int unsigned ui;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "ui");
}

TEST(ParserSection4, IntSignedDecl) {
  // int signed -- explicit signed (default for int)
  auto r = Parse(
      "module m;\n"
      "  int signed si;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(ParserSection4, LogicSignedDecl) {
  // logic signed -- unsigned by default, override to signed
  auto r = Parse(
      "module m;\n"
      "  logic signed [7:0] sv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(ParserSection4, RegUnsignedDecl) {
  auto r = Parse(
      "module m;\n"
      "  reg unsigned [3:0] ru;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed);
}

// --- Multiple integer declarations ---

TEST(ParserSection4, MultipleIntDeclsCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  int a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection4, IntWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection4, All2StateTypes) {
  // Verify all 2-state types parse correctly together
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  byte b;\n"
      "  shortint si;\n"
      "  int i;\n"
      "  longint li;\n"
      "  bit bv;\n"
      "endmodule\n"));
}

TEST(ParserSection4, All4StateTypes) {
  // Verify all 4-state types parse correctly together
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  logic l;\n"
      "  reg r;\n"
      "  integer ig;\n"
      "  time t;\n"
      "endmodule\n"));
}

// =============================================================================
// LRM section 6.12 -- Real, shortreal, and realtime data types (§4.4 Reals)
// =============================================================================

TEST(ParserSection4, RealDecl) {
  // real is same as C double (LRM 6.12)
  auto r = Parse(
      "module m;\n"
      "  real r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(item->name, "r");
}

TEST(ParserSection4, ShortrealDecl) {
  // shortreal is same as C float (LRM 6.12)
  auto r = Parse(
      "module m;\n"
      "  shortreal sr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_EQ(item->name, "sr");
}

TEST(ParserSection4, RealtimeDecl) {
  // realtime is synonymous with real (LRM 6.12)
  auto r = Parse(
      "module m;\n"
      "  realtime rt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
  EXPECT_EQ(item->name, "rt");
}

TEST(ParserSection4, RealWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  real pi = 3.14159;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection4, ShortrealWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  shortreal f = 1.5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection4, MultipleRealDecls) {
  auto r = Parse(
      "module m;\n"
      "  real a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection4, AllRealTypes) {
  // All three real-family types in one module
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r;\n"
      "  shortreal sr;\n"
      "  realtime rt;\n"
      "endmodule\n"));
}

// =============================================================================
// LRM section 5.7/5.8 -- Real literals (§4.4.1 Real literals)
// =============================================================================

TEST(ParserSection4, RealLiteralDecimalPoint) {
  // Standard decimal point real literal
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r = 1.5;\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealLiteralScientificNotation) {
  // Scientific notation: 1.3e2 = 130.0
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r = 1.3e2;\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealLiteralNegativeExponent) {
  // Negative exponent: 1.0e-3 = 0.001
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r = 1.0e-3;\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealLiteralPositiveExponent) {
  // Explicit positive exponent
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r = 2.5E+4;\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealLiteralUnderscoresInValue) {
  // Underscores in real literals for readability
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r = 1_000.000_1;\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealLiteralZeroPointSomething) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r = 0.123;\n"
      "endmodule\n"));
}

// =============================================================================
// LRM section 6.12.1 -- Real conversions (§4.4.2 Real conversions)
// =============================================================================

TEST(ParserSection4, RealToIntAssignment) {
  // Implicit conversion from real to integer (rounds, not truncates)
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  initial begin\n"
      "    r = 35.7;\n"
      "    i = r;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection4, IntToRealAssignment) {
  // Implicit conversion from integer to real
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 42;\n"
      "    r = i;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealCastExplicit) {
  // Explicit cast: int'(real_val) (LRM 6.24)
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real r = 3.7;\n"
      "  int i;\n"
      "  initial i = int'(r);\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealInExpression) {
  // Real values in arithmetic expressions
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial begin\n"
      "    a = 1.5;\n"
      "    b = 2.5;\n"
      "    c = a + b;\n"
      "  end\n"
      "endmodule\n"));
}

// =============================================================================
// LRM section 6.12 -- Shortreal (§4.4.2.9 Shortreal)
// =============================================================================

TEST(ParserSection4, ShortrealInModule) {
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

TEST(ParserSection4, ShortrealInFunctionArg) {
  // shortreal as function argument type
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  function shortreal scale(shortreal val, shortreal factor);\n"
      "    return val * factor;\n"
      "  endfunction\n"
      "endmodule\n"));
}

TEST(ParserSection4, ShortrealCast) {
  // Cast to shortreal
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  int i = 42;\n"
      "  shortreal sr;\n"
      "  initial sr = shortreal'(i);\n"
      "endmodule\n"));
}

TEST(ParserSection4, ShortrealInPort) {
  // shortreal as port type (LRM 23.2.2)
  EXPECT_TRUE(ParseOk(
      "module m (input var shortreal in_val,\n"
      "          output var shortreal out_val);\n"
      "  assign out_val = in_val;\n"
      "endmodule\n"));
}

// =============================================================================
// LRM section 6.16 -- String data type (§4.7 String)
// =============================================================================

TEST(ParserSection4, StringDeclBasic) {
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

TEST(ParserSection4, StringDeclWithInitializer) {
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

TEST(ParserSection4, StringDeclEmptyInit) {
  // string initialized to empty string
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  string s = \"\";\n"
      "endmodule\n"));
}

TEST(ParserSection4, StringParameterDecl) {
  // parameter string (LRM 6.16)
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  parameter string DEFAULT_NAME = \"John Smith\";\n"
      "  string myName = DEFAULT_NAME;\n"
      "endmodule\n"));
}

TEST(ParserSection4, StringInFunctionArg) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  function void greet(string name);\n"
      "    $display(\"Hello %s\", name);\n"
      "  endfunction\n"
      "endmodule\n"));
}

TEST(ParserSection4, StringFunctionReturn) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  function string get_msg();\n"
      "    return \"ok\";\n"
      "  endfunction\n"
      "endmodule\n"));
}

TEST(ParserSection4, StringConcatOp) {
  // String concatenation using {} operator
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  string a, b, c;\n"
      "  initial begin\n"
      "    a = \"hello\";\n"
      "    b = \" world\";\n"
      "    c = {a, b};\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection4, StringComparison) {
  // String comparison operators
  EXPECT_TRUE(ParseOk(
      "module m;\n"
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

TEST(ParserSection4, MultipleStringDecls) {
  auto r = Parse(
      "module m;\n"
      "  string x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

// --- Mixed types in one module ---

TEST(ParserSection4, MixedIntegerRealStringTypes) {
  // All major type families coexisting
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  int i;\n"
      "  real r;\n"
      "  shortreal sr;\n"
      "  string s;\n"
      "  byte b;\n"
      "  logic [7:0] l;\n"
      "  integer ig;\n"
      "  realtime rt;\n"
      "endmodule\n"));
}

TEST(ParserSection4, IntegerTypesInProcedural) {
  // All integer types declared inside initial block
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    byte b;\n"
      "    shortint si;\n"
      "    int i;\n"
      "    longint li;\n"
      "    integer ig;\n"
      "    bit bv;\n"
      "    logic l;\n"
      "    reg r;\n"
      "    time t;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection4, RealTypesInProcedural) {
  // All real types declared inside initial block
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    real r;\n"
      "    shortreal sr;\n"
      "    realtime rt;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection4, StringInProcedural) {
  // String declared inside procedural block
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    string s = \"test\";\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n"));
}
