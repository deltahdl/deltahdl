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
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

Stmt* FirstInitialStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// A.6 -- Behavioral statements
// =============================================================================

TEST(ParserAnnexA, A6AlwaysFFWithSensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock &&
        item->always_kind == AlwaysKind::kAlwaysFF)
      found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A6AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A6InitialAndFinalBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"start\");\n"
      "  final $display(\"end\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found_init = false, found_final = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) found_init = true;
    if (item->kind == ModuleItemKind::kFinalBlock) found_final = true;
  }
  EXPECT_TRUE(found_init);
  EXPECT_TRUE(found_final);
}

TEST(ParserAnnexA, A6BlockingAndNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 1; b <= 2; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->stmts.size(), 2u);
  const StmtKind kExpected[] = {StmtKind::kBlockingAssign,
                                StmtKind::kNonblockingAssign};
  for (size_t i = 0; i < 2; i++) {
    EXPECT_EQ(blk->stmts[i]->kind, kExpected[i]);
  }
}

TEST(ParserAnnexA, A6IfElseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; else x = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ParserAnnexA, A6ForLoopParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(ParserAnnexA, A6ForLoopParts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserAnnexA, A6WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) x = x - 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
}

TEST(ParserAnnexA, A6DoWhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin do x = x - 1; while (x > 0); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
}

TEST(ParserAnnexA, A6ForeverLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever #5 clk = ~clk; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(ParserAnnexA, A6RepeatLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin repeat (10) @(posedge clk); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
}

TEST(ParserAnnexA, A6CaseStmtParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default: y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

TEST(ParserAnnexA, A6CaseStmtItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default: y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

TEST(ParserAnnexA, A6ForkJoinVariants) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; #20 b = 1; join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(ParserAnnexA, A6ForkJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(ParserAnnexA, A6ForkJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

TEST(ParserAnnexA, A6EventTrigger) {
  auto r = Parse("module m; initial begin -> ev; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

TEST(ParserAnnexA, A6WaitStmt) {
  auto r = Parse("module m; initial begin wait (ready) x = 1; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserAnnexA, A6DelayControl) {
  auto r = Parse("module m; initial begin #10 x = 1; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(ParserAnnexA, A6EventControl) {
  auto r =
      Parse("module m; initial begin @(posedge clk) x = 1; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

TEST(ParserAnnexA, A6ProceduralAssignForce) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign x = 1; deassign x;\n"
      "    force y = 0; release y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_EQ(blk->stmts.size(), 4u);
  const StmtKind kExpected[] = {StmtKind::kAssign, StmtKind::kDeassign,
                                StmtKind::kForce, StmtKind::kRelease};
  for (size_t i = 0; i < 4; i++) {
    EXPECT_EQ(blk->stmts[i]->kind, kExpected[i]);
  }
}

TEST(ParserAnnexA, A6ReturnStmt) {
  auto r = Parse(
      "module m;\n"
      "  function int f(); return 42; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kReturn);
}

TEST(ParserAnnexA, A6ForeachStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[i]) $display(arr[i]); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
}

TEST(ParserAnnexA, A6DisableStmt) {
  auto r = Parse("module m; initial begin disable blk; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}
