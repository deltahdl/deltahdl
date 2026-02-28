// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static Stmt* InitialBody(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    return item->body;
  }
  return nullptr;
}

static ModuleItem* FirstFunctionDecl(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl) return item;
  }
  return nullptr;
}

namespace {

// ---------------------------------------------------------------------------
// statement ::= [ block_identifier : ] { attribute_instance } statement_item
// ---------------------------------------------------------------------------
// §9.3.5: statement with block_identifier label
TEST(ParserA604, StatementWithLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    my_label: a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->label, "my_label");
}

// §12.3: statement with attribute instance
TEST(ParserA604, StatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
}

// §12.3: statement with attribute having value
TEST(ParserA604, StatementWithAttributeValue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* weight = 10 *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "weight");
  EXPECT_NE(stmt->attrs[0].value, nullptr);
}

// §12.3: statement with multiple attributes
TEST(ParserA604, StatementWithMultipleAttributes) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* foo, bar *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->attrs.size(), 2u);
  EXPECT_EQ(stmt->attrs[0].name, "foo");
  EXPECT_EQ(stmt->attrs[1].name, "bar");
}

// §12.3: statement with label AND attribute
TEST(ParserA604, StatementWithLabelAndAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl: (* mark *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
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
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// §10.4.2: nonblocking_assignment ;
TEST(ParserA604, StmtItemNonblockingAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

// §10.6.1: procedural_continuous_assignment (assign)
TEST(ParserA604, StmtItemProceduralContinuousAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

// §12.5: case_statement
TEST(ParserA604, StmtItemCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x)\n"
      "      1: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

// §12.4: conditional_statement (if-else)
TEST(ParserA604, StmtItemConditionalStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x) a = 1; else a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

// §13: subroutine_call_statement
TEST(ParserA604, StmtItemSubroutineCallStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

// §9.6.2: disable_statement
TEST(ParserA604, StmtItemDisableStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable my_block;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

// §15.5.1: event_trigger (->)
TEST(ParserA604, StmtItemEventTrigger) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> my_event;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

// §12.7: loop_statement (for)
TEST(ParserA604, StmtItemLoopStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) a = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

// §12.8: jump_statement (break)
TEST(ParserA604, StmtItemJumpStatementBreak) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  VerifyForeverLoopJump(body, StmtKind::kBreak);
}

// §12.8: jump_statement (continue)
TEST(ParserA604, StmtItemJumpStatementContinue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      continue;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  VerifyForeverLoopJump(body, StmtKind::kContinue);
}

// §12.8: jump_statement (return)
TEST(ParserA604, StmtItemJumpStatementReturn) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kReturn);
}

// §9.3.2: par_block (fork-join)
TEST(ParserA604, StmtItemParBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
}

// §9.4: procedural_timing_control_statement (delay)
TEST(ParserA604, StmtItemProceduralTimingControlDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

}  // namespace
