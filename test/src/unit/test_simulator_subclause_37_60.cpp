#include <gtest/gtest.h>

#include <deque>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "fixture_vpi_run.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class AtomicStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(AtomicStatement, DiagramMembersAreAtomicStatements) {
  for (int type : {vpiIf,
                   vpiIfElse,
                   vpiWhile,
                   vpiRepeat,
                   vpiWait,
                   vpiCase,
                   vpiFor,
                   vpiDelayControl,
                   vpiEventControl,
                   vpiEventStmt,
                   vpiAssignment,
                   vpiAssignStmt,
                   vpiDeassign,
                   vpiDisable,
                   vpiTaskCall,
                   vpiSysTaskCall,
                   vpiMethodTaskCall,
                   vpiForever,
                   vpiForce,
                   vpiRelease,
                   vpiDoWhile,
                   vpiExpectStmt,
                   vpiForeachStmt,
                   vpiImmediateAssert,
                   vpiImmediateAssume,
                   vpiImmediateCover,
                   vpiReturnStmt,
                   vpiBreak,
                   vpiContinue,
                   vpiNullStmt}) {
    EXPECT_TRUE(VpiIsAtomicStmtType(type)) << "type constant " << type;
  }
}

TEST_F(AtomicStatement, NonStatementKindsAreNotAtomicStatements) {
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiModule));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiNet));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiConstant));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiBegin));
}

TEST_F(AtomicStatement, LabeledStatementReportsItsLabel) {
  VpiObject stmt;
  stmt.type = vpiIf;
  stmt.name = "check_it";
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&stmt)), "check_it");
}

TEST_F(AtomicStatement, EmptyLabelIsTreatedAsNoLabel) {
  VpiObject stmt;
  stmt.type = vpiWhile;
  stmt.name = "";
  EXPECT_EQ(vpi_get_str(vpiName, VpiHandleOf(&stmt)), nullptr);
}

TEST_F(AtomicStatement, EmptyNameNullingDoesNotApplyToNonAtomicObjects) {
  VpiObject non_stmt;
  non_stmt.type = vpiModule;
  non_stmt.name = "";
  const char* result = vpi_get_str(vpiName, VpiHandleOf(&non_stmt));
  ASSERT_NE(result, nullptr);
  EXPECT_STREQ(result, "");
}

TEST_F(AtomicStatement, TheMembersOfTheClassHaveConstantsOfTheirOwn) {
  EXPECT_EQ(vpiImmediateAssert, 665);
  EXPECT_EQ(vpiImmediateAssume, 694);
  EXPECT_EQ(vpiImmediateCover, 695);
  EXPECT_EQ(vpiReturnStmt, 691);

  EXPECT_NE(vpiImmediateAssume, vpiReturn);
  EXPECT_NE(vpiImmediateCover, vpiAnyPattern);
  EXPECT_NE(vpiImmediateAssume, vpiReturnStmt);
}

TEST_F(AtomicStatement, AFunctionCallWrittenAsAStatementIsOne) {
  for (int type : {vpiFuncCall, vpiMethodFuncCall, vpiSysFuncCall}) {
    VpiObject call;
    call.type = type;
    EXPECT_FALSE(VpiIsAtomicStmtObject(&call)) << type;
    EXPECT_TRUE(VpiIsOperandObject(&call)) << type;
    call.written_as_stmt = true;
    EXPECT_TRUE(VpiIsAtomicStmtObject(&call)) << type;
    EXPECT_FALSE(VpiIsOperandObject(&call)) << type;
  }
}

TEST_F(AtomicStatement, ALoopTellsItsConditionCallFromItsBodyCall) {
  VpiObject condition;
  condition.type = vpiFuncCall;
  VpiObject body;
  body.type = vpiFuncCall;
  body.written_as_stmt = true;
  VpiObject loop;
  loop.type = vpiDoWhile;
  loop.children = {&body, &condition};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&loop))),
            &condition);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&loop))), &body);
}

TEST_F(AtomicStatement, AnIfElseReachesAnElseCallStatement) {
  VpiObject condition;
  condition.type = vpiSysFuncCall;
  VpiObject then_call;
  then_call.type = vpiFuncCall;
  then_call.written_as_stmt = true;
  VpiObject else_call;
  else_call.type = vpiMethodFuncCall;
  else_call.written_as_stmt = true;
  VpiObject branch;
  branch.type = vpiIfElse;
  branch.children = {&condition, &then_call, &else_call};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&branch))),
            &condition);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&branch))), &then_call);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&branch))),
            &else_call);
}

TEST_F(AtomicStatement, ACaseItemsCallStatementIsNoMatchExpression) {
  VpiObject match;
  match.type = vpiFuncCall;
  VpiObject action;
  action.type = vpiFuncCall;
  action.written_as_stmt = true;
  VpiObject item;
  item.type = vpiCaseItem;
  item.children = {&match, &action};
  vpiHandle it = vpi_iterate(vpiExpr, VpiHandleOf(&item));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &match);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

class AtomicStatementsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle First(int type, vpiHandle ref) {
    vpiHandle it = vpi_iterate(type, ref);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

TEST_F(AtomicStatementsOfARun, ALabeledStatementReportsItsLabel) {
  Run("module top; event e; initial trig: -> e; endmodule\n");
  vpiHandle stmt = First(vpiEventStmt, By("top.trig"));
  ASSERT_NE(stmt, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, stmt), "trig");
}

TEST_F(AtomicStatementsOfARun, ALabelledCallIsNamedByItsLabel) {
  Run("module top; task t; endtask\n"
      "  initial l1: t();\n"
      "endmodule\n");
  vpiHandle call = First(vpiTaskCall, By("top.l1"));
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiTaskCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "l1");
  vpiHandle task = vpi_handle(vpiTask, call);
  ASSERT_NE(task, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, task), "t");
}

TEST_F(AtomicStatementsOfARun, AnUnlabelledCallStatementHasNoName) {
  Run("module top; task t; endtask int q[$];\n"
      "  initial begin : b t(); $display(\"hi\"); q.delete(); end\n"
      "endmodule\n");
  vpiHandle task = First(vpiTaskCall, By("top.b"));
  vpiHandle display = First(vpiSysTaskCall, By("top.b"));
  vpiHandle method = First(vpiMethodFuncCall, By("top.b"));
  ASSERT_NE(task, nullptr);
  ASSERT_NE(display, nullptr);
  ASSERT_NE(method, nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, task), nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, display), nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, method), nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiTask, task)), "t");
}

TEST_F(AtomicStatementsOfARun, ACallWithinAnExpressionIsNamedAfterItsCallee) {
  Run("module top; function int f(int a); return a; endfunction int r;\n"
      "  initial begin : b r = f(1); end\n"
      "endmodule\n");
  vpiHandle assign = First(vpiAssignment, By("top.b"));
  ASSERT_NE(assign, nullptr);
  vpiHandle call = vpi_handle(vpiRhs, assign);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "f");
}

TEST_F(AtomicStatementsOfARun, AnUnlabeledStatementReportsNoLabel) {
  Run("module top; event e; initial -> e; endmodule\n");
  vpiHandle stmt = First(vpiEventStmt, By("top"));
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, stmt), nullptr);
}

TEST_F(AtomicStatementsOfARun, ANullStatementIsAnObjectOfTheRun) {
  Run("module top; initial ; endmodule\n");
  vpiHandle proc = First(vpiProcess, By("top"));
  ASSERT_NE(proc, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, proc);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiNullStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, body)), VpiObjectOf(proc));
}

TEST_F(AtomicStatementsOfARun, ABreakAndAContinueAreObjectsOfTheRun) {
  Run("module top; initial for (int i = 0; i < 2; i++) begin : lp\n"
      "  if (i == 0) continue;\n"
      "  break;\n"
      "end endmodule\n");
  vpiHandle lp = By("top.lp");
  ASSERT_NE(lp, nullptr);
  vpiHandle branch = First(vpiIf, lp);
  ASSERT_NE(branch, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, branch)), vpiContinue);
  EXPECT_EQ(KindsOf(vpiBreak, lp), std::vector<int>{vpiBreak});
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, First(vpiBreak, lp))),
            VpiObjectOf(First(vpiProcess, By("top"))));
}

class StatementFill : public ::testing::Test {
 protected:
  static void Name(Expr& expr, std::string_view text) {
    expr.kind = ExprKind::kIdentifier;
    expr.text = text;
  }

  std::deque<VpiObject> made_;
  std::deque<std::string> kept_;
  Arena arena_;
  VpiAttachBuild build_{[this] { return &made_.emplace_back(); },
                        [this](std::string name) {
                          kept_.push_back(std::move(name));
                          return std::string_view(kept_.back());
                        },
                        arena_};
  VpiStmtBuild with_{
      build_,
      [this](const Expr* expr) -> VpiObject* {
        if (expr == nullptr || expr->kind != ExprKind::kIdentifier) {
          return nullptr;
        }
        VpiObject* made = &made_.emplace_back();
        made->type = vpiNet;
        made->name = expr->text;
        return made;
      },
      [](const Stmt*, VpiObject*) -> VpiObject* { return nullptr; },
      [](const Expr*) { return vpiIntVar; },
      [this](const Expr* expr, const VpiObject*) {
        return with_.expression(expr);
      },
      [](int, std::string_view, std::string_view) -> VpiObject* {
        return nullptr;
      }};
};

TEST_F(StatementFill, AnAssignmentMissingASideIsAPlainAssignment) {
  Expr a;
  Name(a, "a");
  Stmt no_rhs;
  no_rhs.kind = StmtKind::kBlockingAssign;
  no_rhs.lhs = &a;
  VpiObject plain;
  plain.type = vpiAssignment;
  VpiFillStmt(&plain, no_rhs, with_);
  EXPECT_EQ(plain.op_type, vpiAssignmentOp);
  EXPECT_EQ(plain.rhs, nullptr);

  Expr b;
  Name(b, "b");
  Expr sum;
  sum.kind = ExprKind::kBinary;
  sum.op = TokenKind::kPlusEq;
  sum.rhs = &b;
  Stmt no_lhs;
  no_lhs.kind = StmtKind::kBlockingAssign;
  no_lhs.rhs = &sum;
  VpiObject whole;
  whole.type = vpiAssignment;
  VpiFillStmt(&whole, no_lhs, with_);
  EXPECT_EQ(whole.op_type, vpiAssignmentOp);
  EXPECT_EQ(whole.rhs, nullptr);
}

TEST_F(StatementFill, AnUnmodelledIntraAssignmentDelayReachesNoDelay) {
  Expr a;
  Name(a, "a");
  Expr b;
  Name(b, "b");
  Expr two;
  two.kind = ExprKind::kIntegerLiteral;
  Stmt stmt;
  stmt.kind = StmtKind::kNonblockingAssign;
  stmt.lhs = &a;
  stmt.rhs = &b;
  stmt.delay = &two;
  VpiObject assignment;
  assignment.type = vpiAssignment;
  VpiFillStmt(&assignment, stmt, with_);
  ASSERT_EQ(assignment.children.size(), 1U);
  EXPECT_EQ(assignment.children[0]->type, vpiDelayControl);
  EXPECT_TRUE(assignment.children[0]->children.empty());
}

TEST_F(StatementFill, AReturnStatementHoldsTheValueItReturns) {
  Expr value;
  Name(value, "v");
  Stmt with_value;
  with_value.kind = StmtKind::kReturn;
  with_value.expr = &value;
  EXPECT_EQ(VpiBuiltStmtKind(with_value), vpiReturnStmt);
  VpiObject returns;
  returns.type = vpiReturnStmt;
  VpiFillStmt(&returns, with_value, with_);
  ASSERT_EQ(returns.children.size(), 1U);
  EXPECT_EQ(returns.children[0]->name, "v");

  Stmt bare;
  bare.kind = StmtKind::kReturn;
  VpiObject returns_nothing;
  returns_nothing.type = vpiReturnStmt;
  VpiFillStmt(&returns_nothing, bare, with_);
  EXPECT_TRUE(returns_nothing.children.empty());
}

TEST_F(StatementFill, AnEventLeftOutLeavesTheControlNoCondition) {
  Expr clk;
  Name(clk, "clk");
  Expr one;
  one.kind = ExprKind::kIntegerLiteral;
  EventExpr modelled;
  modelled.signal = &clk;
  EventExpr posedge;
  posedge.signal = &one;
  posedge.edge = Edge::kPosedge;
  EventExpr guarded;
  guarded.signal = &clk;
  guarded.iff_condition = &one;
  const std::vector<EventExpr> kLeftOut = {posedge, guarded};
  for (const EventExpr& left_out : kLeftOut) {
    Stmt stmt;
    stmt.kind = StmtKind::kEventControl;
    stmt.events = {modelled, left_out};
    VpiObject control;
    control.type = vpiEventControl;
    VpiFillStmt(&control, stmt, with_);
    EXPECT_TRUE(control.children.empty());
  }
}

TEST_F(StatementFill, ACasexOrCasezMatchesIsTaggedOfItsType) {
  Expr sel;
  Name(sel, "sel");
  const std::vector<std::pair<TokenKind, int>> kKeywords = {
      {TokenKind::kKwCasex, vpiCaseX}, {TokenKind::kKwCasez, vpiCaseZ}};
  for (const auto& [keyword, type] : kKeywords) {
    Stmt stmt;
    stmt.kind = StmtKind::kCase;
    stmt.case_kind = keyword;
    stmt.case_matches = true;
    stmt.condition = &sel;
    VpiObject made;
    made.type = vpiCase;
    VpiFillStmt(&made, stmt, with_);
    EXPECT_EQ(made.case_type, type);
    EXPECT_EQ(made.qualifier, vpiTaggedQualifier);
  }
}

TEST_F(StatementFill, AForInitializingNothingDeclaresNoVariable) {
  Stmt stmt;
  stmt.kind = StmtKind::kFor;
  VpiObject loop;
  loop.type = vpiFor;
  loop.local_var_decls = true;
  VpiFillStmt(&loop, stmt, with_);
  EXPECT_FALSE(loop.local_var_decls);
}

TEST_F(StatementFill, ADisableOfNoBlockOrTaskHasNoTarget) {
  VpiObject block;
  block.type = vpiNamedBegin;
  block.name = "b";
  VpiObject var;
  var.type = vpiIntVar;
  var.name = "x";
  var.parent = &block;
  block.children = {&var};
  Expr b;
  Name(b, "b");
  Expr x;
  Name(x, "x");
  Expr literal;
  literal.kind = ExprKind::kIntegerLiteral;
  literal.text = "b";
  Expr no_member;
  no_member.kind = ExprKind::kMemberAccess;
  no_member.lhs = &b;
  Expr off_literal;
  off_literal.kind = ExprKind::kMemberAccess;
  off_literal.lhs = &literal;
  off_literal.rhs = &b;
  const auto kTarget = [&block](Expr* name) {
    Stmt stmt;
    stmt.kind = StmtKind::kDisable;
    stmt.expr = name;
    VpiObject disable;
    disable.type = vpiDisable;
    disable.parent = &block;
    const VpiStmtObjects kStmts{{{&stmt, ""}, &disable}};
    VpiResolveDisableTargets(kStmts);
    return disable.disable_target;
  };
  EXPECT_EQ(kTarget(&b), &block);
  for (Expr* name :
       std::vector<Expr*>{nullptr, &literal, &no_member, &off_literal, &x}) {
    EXPECT_EQ(kTarget(name), nullptr);
  }
}

TEST(StatementKind, AProceduralConcurrentCoverIsACover) {
  Stmt stmt;
  stmt.kind = StmtKind::kCoverImmediate;
  EXPECT_EQ(VpiBuiltStmtKind(stmt), vpiImmediateCover);
  stmt.is_procedural_concurrent = true;
  EXPECT_EQ(VpiBuiltStmtKind(stmt), vpiCover);
}

TEST_F(StatementFill, APropertySpecIsMadeOnlyForAPropertyRead) {
  Expr a;
  Name(a, "a");
  PropertyExprNode tree;
  tree.boolean = &a;
  ModuleItem sequence;
  Stmt property;
  property.kind = StmtKind::kAssertImmediate;
  VpiObject holder;
  holder.type = vpiAssert;
  EXPECT_EQ(VpiMakePropertySpec(&holder, property, with_), nullptr);
  EXPECT_TRUE(holder.children.empty());
  property.assert_property = &tree;
  EXPECT_NE(VpiMakePropertySpec(&holder, property, with_), nullptr);
  property.assert_sequence = &sequence;
  EXPECT_NE(VpiMakePropertySpec(&holder, property, with_), nullptr);
  EXPECT_EQ(holder.children.size(), 2U);
}

TEST_F(StatementFill, ANegatedBooleanPropertyIsANotOperation) {
  Expr a;
  Name(a, "a");
  Stmt property;
  property.kind = StmtKind::kAssertImmediate;
  property.assert_expr = &a;
  property.assert_negated = true;
  VpiObject holder;
  holder.type = vpiAssert;
  const VpiObject* spec = VpiMakePropertySpec(&holder, property, with_);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->children.size(), 1U);
  const VpiObject* negation = spec->children[0];
  EXPECT_EQ(negation->op_type, vpiNotOp);
  ASSERT_EQ(negation->children.size(), 1U);
  EXPECT_EQ(negation->children[0]->name, "a");
}

}  // namespace
}  // namespace delta
