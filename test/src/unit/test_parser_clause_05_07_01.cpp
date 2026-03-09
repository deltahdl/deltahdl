#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_7_1_UnsizedDecimal) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 659;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 659u);
}

TEST(ParserClause05, Cl5_7_1_DecimalZero) {
  auto r = Parse("module m; int x; initial x = 0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0u);
}

TEST(ParserClause05, Cl5_7_1_SizedBinary) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 4'b1001;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0b1001u);
}

TEST(ParserClause05, Cl5_7_1_SizedHex) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 8'hFF;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xFFu);
}

TEST(ParserClause05, Cl5_7_1_SizedOctal) {
  EXPECT_TRUE(ParseOk("module m; initial x = 8'o77; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_SizedDecimal) {
  EXPECT_TRUE(ParseOk("module m; initial x = 5'D3; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_UnsizedHex) {
  EXPECT_TRUE(ParseOk("module m; initial x = 'h837FF; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_LargeUnsizedHex) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [63:0] big;\n"
              "  initial big = 'h7_0000_0000;\n"
              "endmodule"));
}

TEST(ParserClause05, Cl5_7_1_SignedLiteral) {
  EXPECT_TRUE(ParseOk("module m; initial x = 4'shf; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_SignedDecimalQuestion) {
  EXPECT_TRUE(ParseOk("module m; initial x = 16'sd?; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_NegativeUnsized) {
  EXPECT_TRUE(ParseOk("module m; initial x = -8'd6; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_XValue) {
  EXPECT_TRUE(ParseOk("module m; initial x = 12'hx; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_ZValue) {
  EXPECT_TRUE(ParseOk("module m; initial x = 16'hz; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_QuestionMark) {
  EXPECT_TRUE(ParseOk("module m; initial x = 4'b?; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_DecimalXDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dx; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserClause05, Cl5_7_1_DecimalZDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserClause05, Cl5_7_1_UnderscoreInBinary) {
  EXPECT_TRUE(
      ParseOk("module m; initial x = 16'b0011_0101_0001_1111; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_UnderscoreInDecimal) {
  auto r = Parse("module m; int x; initial x = 1_000_000; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1000000u);
}

TEST(ParserClause05, Cl5_7_1_SpaceBetweenBaseAndDigits) {
  EXPECT_TRUE(ParseOk("module m; initial x = 32 'h 12ab_f001; endmodule"));
}

TEST(ParserClause05, Cl5_7_1_DecimalBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'd99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(ParserClause05, Cl5_7_1_DecimalBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'D99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(ParserClause05, Cl5_7_1_BinaryBaseLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(ParserClause05, Cl5_7_1_BinaryBaseUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'B1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(ParserClause05, Cl5_7_1_OctalBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(ParserClause05, Cl5_7_1_OctalBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'O77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(ParserClause05, Cl5_7_1_HexBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'hAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(ParserClause05, Cl5_7_1_HexBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'HAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(ParserClause05, Cl5_7_1_SignedDecimalLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'sd99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(ParserClause05, Cl5_7_1_SignedDecimalUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SD99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(ParserClause05, Cl5_7_1_SignedBinaryLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'sb1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(ParserClause05, Cl5_7_1_SignedBinaryUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'SB1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(ParserClause05, Cl5_7_1_SignedOctalLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'so77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(ParserClause05, Cl5_7_1_SignedOctalUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SO77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(ParserClause05, Cl5_7_1_SignedHexLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'shAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(ParserClause05, Cl5_7_1_SignedHexUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SHAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(ParserClause05, Cl5_7_1_HexDigitLowercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'habcdef; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

TEST(ParserClause05, Cl5_7_1_HexDigitUppercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'hABCDEF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

TEST(ParserClause05, Cl5_7_1_OctalDigitAll) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'o01234567; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 01234567u);
}

TEST(ParserClause05, Cl5_7_1_BinaryDigitZeroOne) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b0101; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 5u);
}

TEST(ParserClause05, Cl5_7_1_DecimalDigitAll) {
  auto r = Parse("module m; int x; initial x = 1234567890; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1234567890u);
}

TEST(ParserClause05, Cl5_7_1_UnbasedUnsizedZero) {
  auto r = Parse("module m; logic x; initial x = '0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserClause05, Cl5_7_1_UnbasedUnsizedOne) {
  auto r = Parse("module m; logic x; initial x = '1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserClause05, Cl5_7_1_UnbasedUnsizedX) {
  auto r = Parse("module m; logic x; initial x = 'x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserClause05, Cl5_7_1_UnbasedUnsizedZ) {
  auto r = Parse("module m; logic x; initial x = 'z; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserClause05, Cl5_7_1_UnbasedUnsizedInAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = '1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserClause05, Cl5_7_1_BinaryValueWithUnderscores) {
  auto r =
      Parse("module m; logic [7:0] x; initial x = 8'b1010_1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xAAu);
}

TEST(ParserClause05, Cl5_7_1_OctalValueWithUnderscores) {
  auto r =
      Parse("module m; logic [11:0] x; initial x = 12'o77_77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 07777u);
}

TEST(ParserClause05, Cl5_7_1_HexValueWithUnderscores) {
  auto r =
      Parse("module m; logic [15:0] x; initial x = 16'hAB_CD; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDu);
}

TEST(ParserClause05, Cl5_7_1_Size1Bit) {
  auto r = Parse("module m; logic x; initial x = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1u);
}

TEST(ParserClause05, Cl5_7_1_Size32Bit) {
  auto r = Parse("module m; int x; initial x = 32'd100; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 100u);
}

TEST(ParserClause05, Cl5_7_1_ConstantPrimaryInteger) {
  auto r = Parse("module m; parameter int P = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserClause05, Cl5_7_1_MultipleLiterals) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 42; b = 8'hFF; c = 4'b1010; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

struct ParseDiag50701 {
  SourceManager mgr;
  Arena arena;
  DiagEngine* diag = nullptr;
  CompilationUnit* cu = nullptr;
};

static ParseDiag50701 ParseWithDiag(const std::string& src) {
  ParseDiag50701 result;
  auto fid = result.mgr.AddFile("<test>", src);
  result.diag = new DiagEngine(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, *result.diag);
  Parser parser(lexer, result.arena, *result.diag);
  result.cu = parser.Parse();
  return result;
}

TEST(ParserClause05, Cl5_7_1_SizedNoOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserClause05, Cl5_7_1_SizedOverflowWarning) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hFF;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

TEST(ParserClause05, Cl5_7_1_SizedExactFit) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserClause05, Cl5_7_1_SizedOneBitOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 3'b1111;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

}
