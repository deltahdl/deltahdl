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

}  // namespace
