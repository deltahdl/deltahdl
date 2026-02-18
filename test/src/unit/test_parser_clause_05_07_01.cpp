#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- §5.7.1 Integer literal constants ---

struct ParseResult50701 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50701 Parse(const std::string& src) {
  ParseResult50701 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult50701& r) {
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

// From test_parser_clause_05.cpp

TEST(ParserCh50701, SizedLiteral_NoOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserCh50701, SizedLiteral_Overflow_Warning) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hFF;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

TEST(ParserCh50701, SizedLiteral_ExactFit) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserCh50701, SizedLiteral_OneBitOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 3'b1111;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
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

TEST(ParserCh50701, IntLiteral_SizedOctal) {
  EXPECT_TRUE(ParseOk("module m; initial x = 8'o77; endmodule"));
}

TEST(ParserCh50701, IntLiteral_SignedLiteral) {
  // 4'shf is a signed 4-bit number (value -1 in two's complement).
  EXPECT_TRUE(ParseOk("module m; initial x = 4'shf; endmodule"));
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

TEST(ParserCh50701, IntLiteral_UnbasedUnsized_Zero) {
  // '0 sets all bits to 0.
  EXPECT_TRUE(ParseOk("module m; initial x = '0; endmodule"));
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

TEST(ParserCh50701, IntLiteral_SpaceBetweenBaseAndDigits) {
  // Space between base format and unsigned number is legal.
  EXPECT_TRUE(ParseOk("module m; initial x = 32 'h 12ab_f001; endmodule"));
}

TEST(ParserCh50701, IntLiteral_LargeUnsized) {
  // 'h7_0000_0000 requires at least 35 bits.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [63:0] big;\n"
              "  initial big = 'h7_0000_0000;\n"
              "endmodule"));
}
