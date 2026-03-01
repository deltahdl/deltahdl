// §12.5.3: unique-case, unique0-case, and priority-case

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// §4.6: unique case statement — exactly one match expected
// =============================================================================
TEST(ParserSection4, Sec4_6_UniqueCaseOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "      2'b10: y = 2;\n"
      "      2'b11: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// =============================================================================
// §4.6: unique0 case statement — at most one match
// =============================================================================
TEST(ParserSection4, Sec4_6_Unique0CaseAtMostOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

// =============================================================================
// §4.6: priority case statement — first match
// =============================================================================
TEST(ParserSection4, Sec4_6_PriorityCaseFirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 19. always_comb with unique case
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_UniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "      2'b11: y = 4'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

struct ParseResult12b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult12b Parse(const std::string& src) {
  ParseResult12b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult12b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// unique casez combines qualifier with casez keyword.
TEST(ParserSection12, UniqueCasezQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique casez (sel)\n"
      "      2'b1?: x = 1;\n"
      "      2'b01: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// ---------------------------------------------------------------------------
// 20. always_comb with priority case
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_PriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] grant;\n"
      "  always_comb begin\n"
      "    priority case (1'b1)\n"
      "      req[0]: grant = 2'd0;\n"
      "      req[1]: grant = 2'd1;\n"
      "      req[2]: grant = 2'd2;\n"
      "      req[3]: grant = 2'd3;\n"
      "      default: grant = 2'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  ASSERT_EQ(stmt->case_items.size(), 5u);
}

// priority casex.
TEST(ParserSection12, PriorityCasex) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority casex (sel)\n"
      "      2'b1?: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

struct ParseResult9j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

// Helper: verify always @* case statement pattern.
static Stmt* GetAlwaysStarCaseStmt(ParseResult9j& r) {
  EXPECT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  EXPECT_NE(item, nullptr);
  if (!item) return nullptr;
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto* case_stmt = item->body->stmts[0];
  EXPECT_EQ(case_stmt->kind, StmtKind::kCase);
  return case_stmt;
}

struct ParseResult9k {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9k Parse(const std::string& src) {
  ParseResult9k result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysItem(ParseResult9k& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

// @* with unique case
TEST(ParserSection9, Sec9_4_2_3_AtStarUniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg out;\n"
      "  always @* begin\n"
      "    unique case (sel)\n"
      "      2'b00: out = 0;\n"
      "      2'b01: out = 1;\n"
      "      default: out = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  auto* case_stmt = GetAlwaysStarCaseStmt(r);
  ASSERT_NE(case_stmt, nullptr);
  EXPECT_EQ(case_stmt->qualifier, CaseQualifier::kUnique);
}

// =============================================================================
// §4.6: Priority case with default
// =============================================================================
TEST(ParserSection4, Sec4_6_PriorityCaseWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (opcode)\n"
      "      4'h0: result = a + b;\n"
      "      4'h1: result = a - b;\n"
      "      4'h2: result = a & b;\n"
      "      default: result = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

// =============================================================================
// §4.6: Unique case with multiple matches listed
// =============================================================================
TEST(ParserSection4, Sec4_6_UniqueCaseMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (state)\n"
      "      IDLE: x = 0;\n"
      "      RUN: x = 1;\n"
      "      DONE: x = 2;\n"
      "      ERR: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  EXPECT_EQ(stmt->case_items.size(), 4u);
}

// ---------------------------------------------------------------------------
// 26. always_comb with unique0 case
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_Unique0Case) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique0 case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

TEST(ParserSection12, UniqueCase) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection12, PriorityCase) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      0: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// ---------------------------------------------------------------------------
// unique_priority with case
// ---------------------------------------------------------------------------
// §12.5.3: unique case
TEST(ParserA607, UniqueCaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case(x)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysLatchItem(ParseResult9i& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 14. unique case statement inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_UniqueCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b, c;\n"
      "  always_latch\n"
      "    unique case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      2'b10: q <= c;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique);
}

// =============================================================================
// Combined patterns -- real-world usage patterns from sections 12.4-12.8
// =============================================================================
// Case inside always_comb with unique qualifier.
TEST(ParserSection12, UniqueCaseInsideAlwaysComb) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [1:0] sel;\n"
              "  logic [7:0] out;\n"
              "  always_comb begin\n"
              "    unique case (sel)\n"
              "      2'd0: out = 8'hAA;\n"
              "      2'd1: out = 8'hBB;\n"
              "      2'd2: out = 8'hCC;\n"
              "      2'd3: out = 8'hDD;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

// §12.5.3: unique0 case
TEST(ParserA607, Unique0CaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 case(x)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

// ---------------------------------------------------------------------------
// 15. priority case statement inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_PriorityCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    priority case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kPriority);
}

// §12.5.3: priority case
TEST(ParserA607, PriorityCaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case(x)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// §12.5.3: priority casez
TEST(ParserA607, PriorityCasezParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority casez(a)\n"
      "      3'b00?: y = 1;\n"
      "      3'b0??: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

// Unique0 case with empty default.
TEST(ParserSection12, Unique0CaseWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

// ---------------------------------------------------------------------------
// 26. unique0 case inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_Unique0CaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    unique0 case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique0);
}

}  // namespace
