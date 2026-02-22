#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult9d Parse(const std::string &src) {
  ParseResult9d result;
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

static Stmt *FirstInitialBody(ParseResult9d &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock)
      return item->body;
  }
  return nullptr;
}

static Stmt *FirstInitialStmt(ParseResult9d &r) {
  auto *body = FirstInitialBody(r);
  if (body && body->kind == StmtKind::kBlock) {
    return body->stmts.empty() ? nullptr : body->stmts[0];
  }
  return body;
}

static ModuleItem *FirstAlwaysItem(ParseResult9d &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks (begin...end)
// Empty and minimal begin-end blocks.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_EmptyBeginEnd) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_TRUE(body->stmts.empty());
}

TEST(ParserSection9, Sec9_3_1_NamedBeginEndMatchingLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin : seq_block\n"
                 "    a = 1;\n"
                 "  end : seq_block\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "seq_block");
  EXPECT_EQ(body->stmts.size(), 1u);
}

TEST(ParserSection9, Sec9_3_1_NamedBeginEndNoEndLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin : blk_no_end\n"
                 "    a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blk_no_end");
}

TEST(ParserSection9, Sec9_3_1_SingleStatementInBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x = 42;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_MultipleAssignmentsInBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a = 1;\n"
                 "    b = 2;\n"
                 "    c = 3;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

// =============================================================================
// LRM section 9.3.1 -- Variable declarations inside sequential blocks.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_VarDeclAsFirstStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int temp;\n"
                 "    temp = 99;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "temp");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_MultipleDifferentTypeVarDecls) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    logic [7:0] y;\n"
                 "    real z;\n"
                 "    x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[3]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_VarDeclWithInitializer) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int count = 10;\n"
                 "    $display(\"%0d\", count);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "count");
  EXPECT_NE(body->stmts[0]->var_init, nullptr);
}

// =============================================================================
// LRM section 9.3.1 -- Nested begin-end blocks.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_NestedBeginEndTwoLevels) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a = 0;\n"
                 "    begin\n"
                 "      b = 1;\n"
                 "      c = 2;\n"
                 "    end\n"
                 "    d = 3;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_DeeplyNestedBeginEndThreeLevels) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    begin\n"
                 "      begin\n"
                 "        a = 1;\n"
                 "      end\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  auto *mid = body->stmts[0];
  EXPECT_EQ(mid->kind, StmtKind::kBlock);
  ASSERT_EQ(mid->stmts.size(), 1u);
  auto *inner = mid->stmts[0];
  EXPECT_EQ(inner->kind, StmtKind::kBlock);
  ASSERT_EQ(inner->stmts.size(), 1u);
  EXPECT_EQ(inner->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_NamedNestedBlocks) {
  auto r = Parse("module m;\n"
                 "  initial begin : outer\n"
                 "    begin : mid\n"
                 "      begin : inner\n"
                 "        x = 1;\n"
                 "      end : inner\n"
                 "    end : mid\n"
                 "  end : outer\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->label, "mid");
  ASSERT_EQ(body->stmts[0]->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->stmts[0]->label, "inner");
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with timing controls.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithDelayControl) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #5 a = 1;\n"
                 "    #10 b = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDelay);
}

TEST(ParserSection9, Sec9_3_1_BlockWithEventControl) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk);\n"
                 "    a = 1;\n"
                 "    @(posedge clk);\n"
                 "    b = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[3]->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with control flow statements.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithIfElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (sel)\n"
                 "      a = 1;\n"
                 "    else\n"
                 "      a = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ParserSection9, Sec9_3_1_BlockWithForLoop) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 8; i++)\n"
                 "      data[i] = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(ParserSection9, Sec9_3_1_BlockWithCaseStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case (mode)\n"
                 "      0: a = 1;\n"
                 "      1: a = 2;\n"
                 "      default: a = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_GE(stmt->case_items.size(), 3u);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with fork-join inside.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithForkJoinInside) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      #10 a = 1;\n"
                 "      #20 b = 2;\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_GE(stmt->fork_stmts.size(), 2u);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with disable of named block.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithDisableOwnName) {
  auto r = Parse("module m;\n"
                 "  initial begin : my_blk\n"
                 "    a = 1;\n"
                 "    disable my_blk;\n"
                 "    b = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "my_blk");
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisable);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with system function calls.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithSystemCalls) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    $display(\"hello\");\n"
                 "    $write(\"world\");\n"
                 "    $finish;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kExprStmt);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with nonblocking assignments.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithNonblockingAssigns) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a <= 1;\n"
                 "    b <= 2;\n"
                 "    c <= 3;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kNonblockingAssign);
  }
}

TEST(ParserSection9, Sec9_3_1_BlockWithMixedBlockingNonblocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    temp = a + b;\n"
                 "    result <= temp;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks in various procedural contexts.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockInAlwaysComb) {
  auto r = Parse("module m;\n"
                 "  always_comb begin\n"
                 "    x = a & b;\n"
                 "    y = a | c;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserSection9, Sec9_3_1_BlockInAlwaysFFWithSensitivity) {
  auto r = Parse("module m;\n"
                 "  always_ff @(posedge clk or negedge rst_n) begin\n"
                 "    if (!rst_n)\n"
                 "      q <= 0;\n"
                 "    else\n"
                 "      q <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  ASSERT_GE(item->sensitivity.size(), 2u);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

TEST(ParserSection9, Sec9_3_1_BlockInFinalBlock) {
  auto r = Parse("module m;\n"
                 "  final begin\n"
                 "    $display(\"sim done\");\n"
                 "    $display(\"cycles: %0d\", cnt);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
      EXPECT_EQ(item->body->kind, StmtKind::kBlock);
      EXPECT_GE(item->body->stmts.size(), 2u);
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// LRM section 9.3.1 -- Automatic and static variable declarations in blocks.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_AutomaticVarDeclInBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    automatic int k = 0;\n"
                 "    k = k + 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_automatic);
  EXPECT_FALSE(body->stmts[0]->var_is_static);
  EXPECT_EQ(body->stmts[0]->var_name, "k");
  EXPECT_NE(body->stmts[0]->var_init, nullptr);
}

TEST(ParserSection9, Sec9_3_1_StaticVarDeclInBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    static int call_count = 0;\n"
                 "    call_count = call_count + 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_static);
  EXPECT_FALSE(body->stmts[0]->var_is_automatic);
  EXPECT_EQ(body->stmts[0]->var_name, "call_count");
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with return statement (inside function).
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithReturnInFunction) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  function int compute(input int a, input int b);\n"
                      "    begin\n"
                      "      int tmp;\n"
                      "      tmp = a + b;\n"
                      "      return tmp;\n"
                      "    end\n"
                      "  endfunction\n"
                      "endmodule\n"));
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with assert immediate.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithAssertImmediate) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a = 1;\n"
                 "    assert (a == 1);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(body->stmts[1]->assert_expr, nullptr);
}

// =============================================================================
// LRM section 9.3.1 -- Block with only variable declarations (no statements).
// =============================================================================

TEST(ParserSection9, Sec9_3_1_BlockWithOnlyVarDecls) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int a;\n"
                 "    logic [3:0] b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
}

// =============================================================================
// LRM section 9.3.1 -- ParseOk smoke tests for complex block scenarios.
// =============================================================================

TEST(ParserSection9, Sec9_3_1_MultipleSequentialBlocksInSameInitial) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    begin : first\n"
                 "      a = 1;\n"
                 "    end : first\n"
                 "    begin : second\n"
                 "      b = 2;\n"
                 "    end : second\n"
                 "    begin : third\n"
                 "      c = 3;\n"
                 "    end : third\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "first");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->label, "second");
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[2]->label, "third");
}
