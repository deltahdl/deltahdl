// §5.7.1: Integer literal constants

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § octal_digit — 0 through 7
TEST(ParserA87, OctalDigitAll) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'o01234567; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 01234567u);
}

// § hex_digit — 0-9, a-f, A-F
TEST(ParserA87, HexDigitLowercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'habcdef; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

TEST(ParserA87, HexDigitUppercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'hABCDEF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

// § x_digit — x
TEST(ParserA87, XDigitLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'hx; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// --- §5.12 Attributes ---
struct ParseResult512 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult512 Parse(const std::string& src) {
  ParseResult512 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult512& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50701, IntLiteral_UnsizedDecimal) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 659;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 659u);
}

TEST(ParserCh50701, IntLiteral_SizedBinary) {
  // 4'b1001 is a 4-bit binary number.
  auto r = Parse(
      "module m;\n"
      "  initial x = 4'b1001;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0b1001u);
}

// § z_digit — Z
TEST(ParserA87, ZDigitUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'hZ; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserCh50701, IntLiteral_SizedHex) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 8'hFF;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xFFu);
}

TEST(ParserCh50701, IntLiteral_UnsizedHex) {
  // 'h 837FF -- unsized hexadecimal.
  EXPECT_TRUE(ParseOk("module m; initial x = 'h837FF; endmodule"));
}

// § z_digit — ?
TEST(ParserA87, ZDigitQuestion) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b?; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserCh50701, IntLiteral_SizedOctal) {
  EXPECT_TRUE(ParseOk("module m; initial x = 8'o77; endmodule"));
}

// § unbased_unsized_literal — '0
TEST(ParserA87, UnbasedUnsizedZero) {
  auto r = Parse("module m; logic x; initial x = '0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserCh50701, IntLiteral_SignedLiteral) {
  // 4'shf is a signed 4-bit number (value -1 in two's complement).
  EXPECT_TRUE(ParseOk("module m; initial x = 4'shf; endmodule"));
}

// § unbased_unsized_literal — '1
TEST(ParserA87, UnbasedUnsizedOne) {
  auto r = Parse("module m; logic x; initial x = '1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserCh50701, IntLiteral_UnbasedUnsized_One) {
  // '1 sets all bits to 1.
  auto r = Parse(
      "module m;\n"
      "  initial x = '1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

// § unbased_unsized_literal — 'x (z_or_x)
TEST(ParserA87, UnbasedUnsizedX) {
  auto r = Parse("module m; logic x; initial x = 'x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserCh50701, IntLiteral_UnbasedUnsized_Zero) {
  // '0 sets all bits to 0.
  EXPECT_TRUE(ParseOk("module m; initial x = '0; endmodule"));
}

// § unbased_unsized_literal — 'z (z_or_x)
TEST(ParserA87, UnbasedUnsizedZ) {
  auto r = Parse("module m; logic x; initial x = 'z; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserCh50701, IntLiteral_Underscore) {
  // Underscores are legal anywhere except as first character.
  EXPECT_TRUE(
      ParseOk("module m; initial x = 16'b0011_0101_0001_1111; endmodule"));
}

TEST(ParserCh50701, IntLiteral_XValue) {
  // 12'hx -- 12-bit unknown.
  EXPECT_TRUE(ParseOk("module m; initial x = 12'hx; endmodule"));
}

TEST(ParserCh50701, IntLiteral_ZValue) {
  // 16'hz -- 16-bit high-impedance.
  EXPECT_TRUE(ParseOk("module m; initial x = 16'hz; endmodule"));
}

TEST(ParserCh50701, IntLiteral_QuestionMark) {
  // ? is an alternative for z in literal constants.
  EXPECT_TRUE(ParseOk("module m; initial x = 16'sd?; endmodule"));
}

TEST(ParserCh50701, IntLiteral_NegativeUnsized) {
  // -8'd6 defines the two's-complement of 6 held in 8 bits.
  EXPECT_TRUE(ParseOk("module m; initial x = -8'd6; endmodule"));
}

TEST(ParserCh50701, IntLiteral_SizedDecimal) {
  // 5'D 3 is a 5-bit decimal number.
  EXPECT_TRUE(ParseOk("module m; initial x = 5'D3; endmodule"));
}

// =============================================================================
// A.8.4 Primaries — primary_literal
// =============================================================================
// § primary_literal — number (decimal)
TEST(ParserA84, PrimaryLiteralDecimalNumber) {
  auto r = Parse("module m; initial x = 100; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserCh50701, IntLiteral_SpaceBetweenBaseAndDigits) {
  // Space between base format and unsigned number is legal.
  EXPECT_TRUE(ParseOk("module m; initial x = 32 'h 12ab_f001; endmodule"));
}

// § primary_literal — number (hex)
TEST(ParserA84, PrimaryLiteralHexNumber) {
  auto r = Parse("module m; initial x = 16'hDEAD; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserCh50701, IntLiteral_LargeUnsized) {
  // 'h7_0000_0000 requires at least 35 bits.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [63:0] big;\n"
              "  initial big = 'h7_0000_0000;\n"
              "endmodule"));
}

// § primary_literal — number (octal)
TEST(ParserA84, PrimaryLiteralOctalNumber) {
  auto r = Parse("module m; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary_literal — number (binary)
TEST(ParserA84, PrimaryLiteralBinaryNumber) {
  auto r = Parse("module m; initial x = 4'b1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary_literal — unbased_unsized_literal
TEST(ParserA84, PrimaryLiteralUnbasedUnsized) {
  auto r = Parse("module m; initial x = '0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserAnnexA, A8IntegerLiterals) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 42; b = 8'hFF; c = 4'b1010; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — constant_primary
// =============================================================================
// § constant_primary — primary_literal (integer)
TEST(ParserA84, ConstantPrimaryIntegerLiteral) {
  auto r = Parse("module m; parameter int P = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param, nullptr);
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kIntegerLiteral);
}

// § constant_primary — unbased_unsized_literal
TEST(ParserA84, ConstantPrimaryUnbasedUnsizedLiteral) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = '1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

// =============================================================================
// A.8.4 Primaries — primary
// =============================================================================
// § primary — primary_literal (integer)
TEST(ParserA84, PrimaryIntegerLiteral) {
  auto r = Parse("module m; initial x = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// =============================================================================
// A.8.7 Numbers — Parser
// =============================================================================
// § number — integral_number
TEST(ParserA87, NumberIntegral) {
  auto r = Parse("module m; logic [7:0] x; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § integral_number — decimal_number (unsized)
TEST(ParserA87, IntegralDecimal) {
  auto r = Parse("module m; int x; initial x = 255; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 255u);
}

// § integral_number — octal_number
TEST(ParserA87, IntegralOctal) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § integral_number — binary_number
TEST(ParserA87, IntegralBinary) {
  auto r =
      Parse("module m; logic [7:0] x; initial x = 8'b10101010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xAAu);
}

// § integral_number — hex_number
TEST(ParserA87, IntegralHex) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xFFu);
}

// § decimal_number — unsigned_number
TEST(ParserA87, DecimalUnsigned) {
  auto r = Parse("module m; int x; initial x = 0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0u);
}

// § decimal_number — [size] decimal_base unsigned_number
TEST(ParserA87, DecimalSizedBase) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'd200; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 200u);
}

// § decimal_number — [size] decimal_base x_digit
TEST(ParserA87, DecimalXDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dx; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § decimal_number — [size] decimal_base z_digit
TEST(ParserA87, DecimalZDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

}  // namespace
