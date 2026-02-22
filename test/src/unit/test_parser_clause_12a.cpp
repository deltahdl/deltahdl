#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
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

static Stmt *InitialBody(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock)
      return item->body;
  }
  return nullptr;
}

// =============================================================================
// LRM section 12.6 -- Named blocks / block labels
// =============================================================================

TEST(ParserSection12, NamedBeginEnd) {
  auto r = Parse("module t;\n"
                 "  initial begin : my_block\n"
                 "    x = 1;\n"
                 "  end : my_block\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

TEST(ParserSection12, NamedBeginEndNoEndLabel) {
  auto r = Parse("module t;\n"
                 "  initial begin : blk\n"
                 "    x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blk");
}

TEST(ParserSection12, NamedForkJoin) {
  auto r = Parse("module t;\n"
                 "  initial fork : my_fork\n"
                 "    x = 1;\n"
                 "  join : my_fork\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->label, "my_fork");
}

TEST(ParserSection12, NamedForkJoinAny) {
  auto r = Parse("module t;\n"
                 "  initial fork : par_blk\n"
                 "    x = 1;\n"
                 "  join_any : par_blk\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->label, "par_blk");
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinAny);
}

TEST(ParserSection12, UnlabeledBlockHasEmptyLabel) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_TRUE(body->label.empty());
}

// =============================================================================
// LRM section 12.4.2 / section 12.5.3 -- unique/priority/unique0 qualifiers
// =============================================================================

TEST(ParserSection12, UniqueIf) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    unique if (a) x = 1;\n"
                 "    else x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection12, PriorityIf) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    priority if (a) x = 1;\n"
                 "    else x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ParserSection12, Unique0If) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    unique0 if (a) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(ParserSection12, UniqueCase) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    unique case (sel)\n"
                 "      0: x = 1;\n"
                 "      1: x = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection12, PriorityCase) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    priority case (sel)\n"
                 "      0: x = 1;\n"
                 "      default: x = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ParserSection12, PlainCaseHasNoQualifier) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    case (sel)\n"
                 "      0: x = 1;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

// =============================================================================
// LRM section 12.5.4 -- case inside
// =============================================================================

TEST(ParserSection12, CaseInside) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    case (val) inside\n"
                 "      0: x = 1;\n"
                 "      1: x = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_TRUE(stmt->case_inside);
}

TEST(ParserSection12, PlainCaseIsNotInside) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    case (val)\n"
                 "      0: x = 1;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_FALSE(stmt->case_inside);
}

// =============================================================================
// LRM section 12.7.3 -- foreach loop
// =============================================================================

TEST(ParserSection12, ForeachBasicParses) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    foreach (arr[i]) x = arr[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection12, ForeachBasicVars) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    foreach (arr[i]) x = arr[i];\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
}

TEST(ParserSection12, ForeachMultipleVars) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    foreach (matrix[i, j]) x = matrix[i][j];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  const std::vector<std::string> kExpected = {"i", "j"};
  for (size_t k = 0; k < kExpected.size(); ++k) {
    EXPECT_EQ(stmt->foreach_vars[k], kExpected[k]);
  }
}

TEST(ParserSection12, ForeachEmptyVar) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    foreach (arr[, j]) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
}

TEST(ParserSection12, ForeachEmptyVarValues) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    foreach (arr[, j]) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

TEST(ParserSection12, ForeachWithBlock) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    foreach (arr[i]) begin\n"
                 "      $display(\"%d\", arr[i]);\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.7.1 -- for with variable declaration
// =============================================================================

TEST(ParserSection12, ForWithIntDeclParses) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i = i + 1) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
}

TEST(ParserSection12, ForWithIntDeclParts) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i = i + 1) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(ParserSection12, ForWithLogicDecl) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (logic [7:0] i = 0; i < 10; i = i + 1) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kLogic);
}

TEST(ParserSection12, ForWithoutDeclStillWorks) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (i = 0; i < 10; i = i + 1) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kImplicit);
}

// =============================================================================
// LRM section 12.5.1 -- casex / casez
// =============================================================================

TEST(ParserSection12, CasexStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    casex (sel)\n"
                 "      2'b1?: x = 1;\n"
                 "      default: x = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  ASSERT_EQ(stmt->case_items.size(), 2u);
}

TEST(ParserSection12, CasezStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    casez (sel)\n"
                 "      2'b1?: x = 1;\n"
                 "      default: x = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  ASSERT_EQ(stmt->case_items.size(), 2u);
}

// =============================================================================
// Combined tests -- qualifiers with named blocks
// =============================================================================

// =============================================================================
// LRM section 12.7.4 -- While loop
// =============================================================================

TEST(ParserSection12, WhileLoop) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    while (x > 0) x = x - 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection12, WhileLoopWithBlock) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    while (x > 0) begin\n"
                 "      x = x - 1;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.7.5 -- Do-while loop
// =============================================================================

TEST(ParserSection12, DoWhileLoop) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    do x = x + 1; while (x < 10);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection12, DoWhileLoopWithBlock) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    do begin\n"
                 "      x = x + 1;\n"
                 "    end while (x < 10);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.7.6 -- Repeat loop
// =============================================================================

TEST(ParserSection12, RepeatLoop) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    repeat (10) x = x + 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// =============================================================================
// LRM section 12.7.7 -- Forever loop
// =============================================================================

TEST(ParserSection12, ForeverLoop) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    forever x = x + 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection12, ForeverLoopWithBlock) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    forever begin\n"
                 "      @(posedge clk);\n"
                 "      x = x + 1;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.8 -- Jump statements (return, break, continue)
// =============================================================================

// Helper: find a function declaration's first return statement.
static Stmt *FindReturnStmt(ParseResult &r) {
  auto *mod = r.cu->modules[0];
  for (auto *item : mod->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl)
      continue;
    for (auto *s : item->func_body_stmts) {
      if (s->kind == StmtKind::kReturn)
        return s;
    }
  }
  return nullptr;
}

TEST(ParserSection12, ReturnWithValue) {
  auto r = Parse("module t;\n"
                 "  function int foo();\n"
                 "    return 42;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *ret = FindReturnStmt(r);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  EXPECT_NE(ret->expr, nullptr);
}

TEST(ParserSection12, ReturnVoid) {
  auto r = Parse("module t;\n"
                 "  function void bar();\n"
                 "    return;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *ret = FindReturnStmt(r);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  EXPECT_EQ(ret->expr, nullptr);
}

TEST(ParserSection12, BreakStatementParses) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    forever begin\n"
                 "      if (done) break;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(ParserSection12, BreakStatementInBody) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    forever begin\n"
                 "      if (done) break;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // The body contains an if whose then_branch is break.
  auto *if_stmt = stmt->body->stmts[0];
  ASSERT_NE(if_stmt, nullptr);
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kBreak);
}

TEST(ParserSection12, ContinueStatementParses) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i = i + 1) begin\n"
                 "      if (i == 5) continue;\n"
                 "      x = i;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  auto *body = stmt->for_body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
}

TEST(ParserSection12, ContinueStatementInBody) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i = i + 1) begin\n"
                 "      if (i == 5) continue;\n"
                 "      x = i;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *body = stmt->for_body;
  ASSERT_NE(body, nullptr);
  auto *if_stmt = body->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kContinue);
}

// =============================================================================
// LRM section 12.9 -- Event trigger (->)
// =============================================================================

TEST(ParserSection12, EventTrigger) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    -> done_event;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

// =============================================================================
// LRM section 12.10 -- Disable statement
// =============================================================================

TEST(ParserSection12, DisableBlock) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    disable my_block;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ParserSection12, DisableFork) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    disable fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisableFork);
}

// =============================================================================
// Combined tests -- qualifiers with named blocks
// =============================================================================

TEST(ParserSection12, UniqueCasexQualifier) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    unique casex (sel)\n"
                 "      2'b1?: x = 1;\n"
                 "      default: x = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// =============================================================================
// LRM section 12.8 -- Block names and statement labels (additional tests)
// =============================================================================

TEST(ParserSection12, StatementLabelOnAssign) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    assign_val: x = 42;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "assign_val");
}

TEST(ParserSection12, StatementLabelOnWhile) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    loop: while (x > 0) x = x - 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
}

TEST(ParserSection12, StatementLabelOnForever) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    inf: forever @(posedge clk) x = ~x;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(ParserSection12, NestedNamedBlocks) {
  auto r = Parse("module t;\n"
                 "  initial begin : outer\n"
                 "    begin : inner\n"
                 "      x = 1;\n"
                 "    end : inner\n"
                 "  end : outer\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->label, "inner");
}

// =============================================================================
// LRM section 12.4 -- Conditional if-else statement
// =============================================================================

TEST(ParserSection12, BasicIfElse) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a) x = 1;\n"
                 "    else x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
}

TEST(ParserSection12, IfWithoutElse) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

TEST(ParserSection12, NestedIfElse) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a)\n"
                 "      if (b) x = 1;\n"
                 "      else x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // Else associates with the inner if
  EXPECT_EQ(stmt->else_branch, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch->else_branch, nullptr);
}

TEST(ParserSection12, IfElseIfChain) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a) x = 1;\n"
                 "    else if (b) x = 2;\n"
                 "    else if (c) x = 3;\n"
                 "    else x = 4;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kIf);
}

TEST(ParserSection12, IfWithBlockBody) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a) begin\n"
                 "      x = 1;\n"
                 "      y = 2;\n"
                 "    end else begin\n"
                 "      x = 3;\n"
                 "      y = 4;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.7.1 -- for-loop (additional coverage)
// =============================================================================

TEST(ParserSection12, ForLoopPostIncrementStep) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserSection12, ForLoopPostDecrementStep) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 255; i >= 0; i--) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserSection12, ForLoopWithBlockBody) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 8; i++) begin\n"
                 "      $display(\"%d\", i);\n"
                 "      x = x + i;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
}
