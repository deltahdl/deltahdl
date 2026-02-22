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
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    return item->body;
  }
  return nullptr;
}

static ModuleItem *FirstFunctionDecl(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl)
      return item;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.6.4 Statements
// =============================================================================

// ---------------------------------------------------------------------------
// statement_or_null ::= statement | { attribute_instance } ;
// ---------------------------------------------------------------------------

// §12.3: null statement (just semicolon)
TEST(ParserA604, NullStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
}

// §12.3: null statement with attribute instance
TEST(ParserA604, NullStatementWithAttribute) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    (* synthesis *) ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  auto *stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kNull);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "synthesis");
}

// §12.3: multiple null statements
TEST(ParserA604, MultipleNullStatements) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    ;\n"
                 "    ;\n"
                 "    ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNull);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kNull);
}

// ---------------------------------------------------------------------------
// statement ::= [ block_identifier : ] { attribute_instance } statement_item
// ---------------------------------------------------------------------------

// §9.3.5: statement with block_identifier label
TEST(ParserA604, StatementWithLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    my_label: a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->label, "my_label");
}

// §12.3: statement with attribute instance
TEST(ParserA604, StatementWithAttribute) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    (* full_case *) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
}

// §12.3: statement with attribute having value
TEST(ParserA604, StatementWithAttributeValue) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    (* weight = 10 *) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "weight");
  EXPECT_NE(stmt->attrs[0].value, nullptr);
}

// §12.3: statement with multiple attributes
TEST(ParserA604, StatementWithMultipleAttributes) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    (* foo, bar *) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->attrs.size(), 2u);
  EXPECT_EQ(stmt->attrs[0].name, "foo");
  EXPECT_EQ(stmt->attrs[1].name, "bar");
}

// §12.3: statement with label AND attribute
TEST(ParserA604, StatementWithLabelAndAttribute) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    lbl: (* mark *) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->label, "lbl");
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "mark");
}

// ---------------------------------------------------------------------------
// statement_item — all 19 alternatives recognized by the dispatcher
// Each sub-alternative is defined in its own subclause; here we verify the
// statement_item dispatch recognizes each one.
// ---------------------------------------------------------------------------

// §10.4.1: blocking_assignment ;
TEST(ParserA604, StmtItemBlockingAssignment) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// §10.4.2: nonblocking_assignment ;
TEST(ParserA604, StmtItemNonblockingAssignment) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x <= 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

// §10.6.1: procedural_continuous_assignment (assign)
TEST(ParserA604, StmtItemProceduralContinuousAssignment) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    assign x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

// §12.5: case_statement
TEST(ParserA604, StmtItemCaseStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case (x)\n"
                 "      1: a = 1;\n"
                 "      default: a = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

// §12.4: conditional_statement (if-else)
TEST(ParserA604, StmtItemConditionalStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (x) a = 1; else a = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

// §13: subroutine_call_statement
TEST(ParserA604, StmtItemSubroutineCallStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    $display(\"hello\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

// §9.6.2: disable_statement
TEST(ParserA604, StmtItemDisableStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    disable my_block;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

// §15.5.1: event_trigger (->)
TEST(ParserA604, StmtItemEventTrigger) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    -> my_event;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

// §12.7: loop_statement (for)
TEST(ParserA604, StmtItemLoopStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++) a = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

// §12.8: jump_statement (break)
TEST(ParserA604, StmtItemJumpStatementBreak) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    forever begin\n"
                 "      break;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  auto *forever_stmt = body->stmts[0];
  ASSERT_NE(forever_stmt, nullptr);
  EXPECT_EQ(forever_stmt->kind, StmtKind::kForever);
  auto *loop_body = forever_stmt->body;
  ASSERT_NE(loop_body, nullptr);
  EXPECT_EQ(loop_body->stmts[0]->kind, StmtKind::kBreak);
}

// §12.8: jump_statement (continue)
TEST(ParserA604, StmtItemJumpStatementContinue) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    forever begin\n"
                 "      continue;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  auto *forever_stmt = body->stmts[0];
  auto *loop_body = forever_stmt->body;
  ASSERT_NE(loop_body, nullptr);
  EXPECT_EQ(loop_body->stmts[0]->kind, StmtKind::kContinue);
}

// §12.8: jump_statement (return)
TEST(ParserA604, StmtItemJumpStatementReturn) {
  auto r = Parse("module m;\n"
                 "  function void f();\n"
                 "    return;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kReturn);
}

// §9.3.2: par_block (fork-join)
TEST(ParserA604, StmtItemParBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      a = 1;\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
}

// §9.4: procedural_timing_control_statement (delay)
TEST(ParserA604, StmtItemProceduralTimingControlDelay) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #10 a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

// §9.4.2: procedural_timing_control_statement (event control)
TEST(ParserA604, StmtItemProceduralTimingControlEvent) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

// §9.3.1: seq_block (begin-end)
TEST(ParserA604, StmtItemSeqBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    begin\n"
                 "      a = 1;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
}

// §9.4.3: wait_statement
TEST(ParserA604, StmtItemWaitStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (done) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// §16.3: procedural_assertion_statement (assert)
TEST(ParserA604, StmtItemProceduralAssertionStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    assert (x == 1);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
}

// §18.16: randcase_statement
TEST(ParserA604, StmtItemRandcaseStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    randcase\n"
                 "      1: a = 1;\n"
                 "      1: a = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
}

// §15.5.1: nonblocking event trigger (->>)
TEST(ParserA604, StmtItemNonblockingEventTrigger) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    ->> my_event;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

// §10.6.1: procedural deassign
TEST(ParserA604, StmtItemProceduralDeassign) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    deassign x;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
}

// §10.6.2: force statement
TEST(ParserA604, StmtItemForceStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    force x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
}

// §10.6.2: release statement
TEST(ParserA604, StmtItemReleaseStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    release x;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

// ---------------------------------------------------------------------------
// function_statement ::= statement
// function_statement_or_null ::= function_statement | { attribute_instance } ;
// ---------------------------------------------------------------------------

// §13: function_statement — regular statement in function body
TEST(ParserA604, FunctionStatement) {
  auto r = Parse("module m;\n"
                 "  function void f();\n"
                 "    a = 1;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kBlockingAssign);
}

// §13: function_statement_or_null — null statement in function body
TEST(ParserA604, FunctionStatementOrNullWithNull) {
  auto r = Parse("module m;\n"
                 "  function void f();\n"
                 "    ;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kNull);
}

// §13: function_statement with label
TEST(ParserA604, FunctionStatementWithLabel) {
  auto r = Parse("module m;\n"
                 "  function void f();\n"
                 "    step1: a = 1;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->label, "step1");
}

// §13: function_statement with attribute
TEST(ParserA604, FunctionStatementWithAttribute) {
  auto r = Parse("module m;\n"
                 "  function void f();\n"
                 "    (* inline *) a = 1;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_FALSE(func->func_body_stmts[0]->attrs.empty());
  EXPECT_EQ(func->func_body_stmts[0]->attrs[0].name, "inline");
}

// §13: multiple function statements including null
TEST(ParserA604, FunctionBodyMultipleStatements) {
  auto r = Parse("module m;\n"
                 "  function void f();\n"
                 "    a = 1;\n"
                 "    ;\n"
                 "    b = 2;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 3u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(func->func_body_stmts[1]->kind, StmtKind::kNull);
  EXPECT_EQ(func->func_body_stmts[2]->kind, StmtKind::kBlockingAssign);
}
