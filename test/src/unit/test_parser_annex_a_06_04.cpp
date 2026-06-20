#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StatementOrNullSyntaxParsing, BareSemicolonIsNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
}

TEST(StatementOrNullSyntaxParsing, NullStmtWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* mark *) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
  ASSERT_GE(body->stmts[0]->attrs.size(), 1u);
  EXPECT_EQ(body->stmts[0]->attrs[0].name, "mark");
}

TEST(StatementOrNullSyntaxParsing, NullStmtWithMultipleAttributeInstances) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* a *) (* b *) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
  ASSERT_GE(body->stmts[0]->attrs.size(), 2u);
  EXPECT_EQ(body->stmts[0]->attrs[0].name, "a");
  EXPECT_EQ(body->stmts[0]->attrs[1].name, "b");
}

TEST(StatementSyntaxParsing, StmtLabelOnAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl_a : x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s->label, "lbl_a");
}

TEST(StatementSyntaxParsing, StmtLabelAndBlockNameClashErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    outer_lbl : begin : inner_name\n"
      "      x = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(StatementSyntaxParsing, AttrPrefixOnAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* keep *) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kBlockingAssign);
  ASSERT_GE(s->attrs.size(), 1u);
  EXPECT_EQ(s->attrs[0].name, "keep");
}

TEST(StatementSyntaxParsing, MultipleAttributeInstancesOnStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* keep *) (* weight = 5 *) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kBlockingAssign);
  ASSERT_GE(s->attrs.size(), 2u);
  EXPECT_EQ(s->attrs[0].name, "keep");
  EXPECT_EQ(s->attrs[1].name, "weight");
}

TEST(StatementSyntaxParsing, LabelAndAttrPrefixCombined) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ll : (* w = 3 *) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->label, "ll");
  ASSERT_GE(s->attrs.size(), 1u);
  EXPECT_EQ(s->attrs[0].name, "w");
}

TEST(StatementItemDispatch, BlockingAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kBlockingAssign);
}

TEST(StatementItemDispatch, NonblockingAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kNonblockingAssign);
}

TEST(StatementItemDispatch, ProcContAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kAssign);
}

TEST(StatementItemDispatch, CaseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (a) default: x = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kCase);
}

TEST(StatementItemDispatch, ConditionalStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kIf);
}

TEST(StatementItemDispatch, SubroutineCallStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hi\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kExprStmt);
}

TEST(StatementItemDispatch, DisableStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable some_block;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kDisable);
}

TEST(StatementItemDispatch, EventTriggerStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kEventTrigger);
}

TEST(StatementItemDispatch, LoopStmtWhile) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    while (cond) x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kWhile);
}

TEST(StatementItemDispatch, JumpStmtBreak) {
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
  auto* forever_stmt = FirstInitialStmt(r);
  ASSERT_NE(forever_stmt, nullptr);
  ASSERT_NE(forever_stmt->body, nullptr);
  ASSERT_GE(forever_stmt->body->stmts.size(), 1u);
  EXPECT_EQ(forever_stmt->body->stmts[0]->kind, StmtKind::kBreak);
}

TEST(StatementItemDispatch, ParBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork x = 1; join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kFork);
}

TEST(StatementItemDispatch, ProcTimingControlStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kDelay);
}

TEST(StatementItemDispatch, SeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin x = 1; end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kBlock);
}

TEST(StatementItemDispatch, WaitStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (cond) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kWait);
}

TEST(StatementItemDispatch, ProcAssertionStmtAssert) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (cond);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kAssertImmediate);
}

TEST(StatementItemDispatch, RandcaseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: x = 1;\n"
      "      2: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kRandcase);
}

TEST(StatementItemDispatch, RandsequenceStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence (top)\n"
      "      top : { x = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kRandsequence);
}

TEST(StatementItemDispatch, ExpectPropertyStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstInitialStmt(r)->kind, StmtKind::kExpect);
}

TEST(StatementItemDispatch, ClockingDriveStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cv <= ##1 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(s->cycle_delay, nullptr);
}

TEST(FunctionStatementOrNullSyntaxParsing, NullStmtAllowedInFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    ;\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  bool saw_null = false;
  for (auto* s : func->func_body_stmts) {
    if (s->kind == StmtKind::kNull) saw_null = true;
  }
  EXPECT_TRUE(saw_null);
}

TEST(FunctionStatementOrNullSyntaxParsing, AttributedNullStmtInFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    (* placeholder *) ;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  Stmt* null_stmt = nullptr;
  for (auto* s : func->func_body_stmts) {
    if (s->kind == StmtKind::kNull) {
      null_stmt = s;
      break;
    }
  }
  ASSERT_NE(null_stmt, nullptr);
  ASSERT_GE(null_stmt->attrs.size(), 1u);
  EXPECT_EQ(null_stmt->attrs[0].name, "placeholder");
}

TEST(FunctionStatementSyntaxParsing, LabelPrefixedStmtInFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    body_lbl : f = 7;\n"
      "    return f;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  Stmt* labeled = nullptr;
  for (auto* s : func->func_body_stmts) {
    if (s->label == "body_lbl") {
      labeled = s;
      break;
    }
  }
  ASSERT_NE(labeled, nullptr);
  EXPECT_EQ(labeled->kind, StmtKind::kBlockingAssign);
}

TEST(FunctionStatementSyntaxParsing, AttrPrefixedStmtInFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    (* keep *) f = 7;\n"
      "    return f;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  Stmt* attributed = nullptr;
  for (auto* s : func->func_body_stmts) {
    if (s->kind == StmtKind::kBlockingAssign && !s->attrs.empty()) {
      attributed = s;
      break;
    }
  }
  ASSERT_NE(attributed, nullptr);
  EXPECT_EQ(attributed->attrs[0].name, "keep");
}

TEST(FunctionStatementOrNullSyntaxParsing, MultipleAttrInstancesOnNullInFunc) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    (* a *) (* b *) ;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  Stmt* null_stmt = nullptr;
  for (auto* s : func->func_body_stmts) {
    if (s->kind == StmtKind::kNull) {
      null_stmt = s;
      break;
    }
  }
  ASSERT_NE(null_stmt, nullptr);
  ASSERT_GE(null_stmt->attrs.size(), 2u);
  EXPECT_EQ(null_stmt->attrs[0].name, "a");
  EXPECT_EQ(null_stmt->attrs[1].name, "b");
}

}  // namespace
