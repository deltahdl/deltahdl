// Tests for A.8.1 — Concatenations — Parser

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.8.1 Concatenations — Parser
// =============================================================================

// § concatenation ::= { expression { , expression } }

TEST(ParserA81, ConcatenationSingleElement) {
  auto r = Parse("module m; initial x = {a}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 1u);
}

TEST(ParserA81, ConcatenationTwoElements) {
  auto r = Parse("module m; initial x = {a, b}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(ParserA81, ConcatenationThreeElements) {
  auto r = Parse("module m; initial x = {a, b, c}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

TEST(ParserA81, ConcatenationNested) {
  auto r = Parse("module m; initial x = {a, {b, c}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
  EXPECT_EQ(stmt->rhs->elements[1]->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements[1]->elements.size(), 2u);
}

// § constant_concatenation ::= { constant_expression { , constant_expression }
// }

TEST(ParserA81, ConstantConcatenation) {
  auto r = Parse("module m;\n"
                 "  parameter P = {8'hAB, 8'hCD};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_multiple_concatenation ::=
//     { constant_expression constant_concatenation }

TEST(ParserA81, ConstantMultipleConcatenation) {
  auto r = Parse("module m;\n"
                 "  parameter P = {4{8'hFF}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § multiple_concatenation ::= { expression concatenation }

TEST(ParserA81, MultipleConcatenationBasic) {
  auto r = Parse("module m; initial x = {4{a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(stmt->rhs->repeat_count, nullptr);
}

TEST(ParserA81, MultipleConcatenationMultipleInner) {
  auto r = Parse("module m; initial x = {2{a, b}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(ParserA81, MultipleConcatenationExprCount) {
  auto r = Parse("module m; initial x = {(N+1){a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

// § streaming_concatenation ::=
//     { stream_operator [ slice_size ] stream_concatenation }

TEST(ParserA81, StreamingConcatLeftShift) {
  auto r = Parse("module m; initial x = {<< {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kLtLt);
}

TEST(ParserA81, StreamingConcatRightShift) {
  auto r = Parse("module m; initial x = {>> {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kGtGt);
}

// § slice_size ::= simple_type | constant_expression

TEST(ParserA81, StreamingWithTypeSliceSize) {
  auto r = Parse("module m; initial x = {<< byte {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

TEST(ParserA81, StreamingWithIntSliceSize) {
  auto r = Parse("module m; initial x = {<< int {a, b}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

TEST(ParserA81, StreamingWithExprSliceSize) {
  auto r = Parse("module m; initial x = {<< 4 {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

// § stream_concatenation ::= { stream_expression { , stream_expression } }

TEST(ParserA81, StreamConcatMultipleElements) {
  auto r = Parse("module m; initial x = {<< {a, b, c}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

// § stream_expression ::= expression [ with [ array_range_expression ] ]

TEST(ParserA81, StreamExpressionWithArrayRange) {
  auto r = Parse("module m; initial x = {<< {a with [3]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

// § array_range_expression ::= expression : expression

TEST(ParserA81, StreamExprWithFixedRange) {
  auto r = Parse("module m; initial x = {<< {a with [3:0]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § array_range_expression ::= expression +: expression

TEST(ParserA81, StreamExprWithPlusRange) {
  auto r = Parse("module m; initial x = {<< {a with [0+:4]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § array_range_expression ::= expression -: expression

TEST(ParserA81, StreamExprWithMinusRange) {
  auto r = Parse("module m; initial x = {<< {a with [7-:4]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § empty_unpacked_array_concatenation ::= { }

TEST(ParserA81, EmptyUnpackedArrayConcatenation) {
  auto r = Parse("module m; initial x = {}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_TRUE(stmt->rhs->elements.empty());
}

// § Postfix select on concatenation (§11.4.12)

TEST(ParserA81, ConcatenationPostfixBitSelect) {
  auto r = Parse("module m; initial x = {a, b}[3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

TEST(ParserA81, ConcatenationPostfixPartSelect) {
  auto r = Parse("module m; initial x = {a, b}[5:2]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

// § module_path_concatenation (in specify context)

TEST(ParserA81, ModulePathConcatenation) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    ({a, b} => c) = 5;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
