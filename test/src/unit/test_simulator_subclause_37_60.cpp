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
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.60 Atomic statement: the object model diagram groups the procedural
// statement kinds under the "atomic stmt" class and gives them one label access
// edge - "-> label", str: vpiName. The clause's sole numbered Detail governs
// that edge: vpiName reports the statement's label when one was written, and
// NULL otherwise. These tests observe the production code that classifies the
// grouping (VpiIsAtomicStmtType) and applies the label rule through the public
// vpi_get_str(vpiName) dispatch path.

// The fixture installs a context so the public vpi_get_str entry point runs its
// real dispatch over the test objects.
class AtomicStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// The grouping: every statement kind drawn inside the atomic stmt class - the
// concrete members standing in for the waits, disables, and tf call groupings -
// is recognized as a member.
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

// Object kinds outside the atomic stmt grouping are not classified as members -
// including a sequential block (vpiBegin), which is a statement container
// rather than an atomic statement.
TEST_F(AtomicStatement, NonStatementKindsAreNotAtomicStatements) {
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiModule));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiNet));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiConstant));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiBegin));
}

// D1: when the statement was written with a label, vpiName reports that label.
TEST_F(AtomicStatement, LabeledStatementReportsItsLabel) {
  VpiObject stmt;
  stmt.type = vpiIf;
  stmt.name = "check_it";  // the statement label
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&stmt)), "check_it");
}

// D1: when no label was given, vpiName is NULL rather than the empty string -
// covering both an unset name and a label recorded as an empty string, since
// the production code treats either as "no label". This is the outcome that
// distinguishes the clause's rule, applied by the production code, from simply
// handing back the stored name pointer.
TEST_F(AtomicStatement, EmptyLabelIsTreatedAsNoLabel) {
  VpiObject stmt;
  stmt.type = vpiWhile;
  stmt.name = "";  // explicitly empty
  EXPECT_EQ(vpi_get_str(vpiName, VpiHandleOf(&stmt)), nullptr);
}

// D1 scope guard: the empty-label-becomes-NULL conversion is specific to atomic
// statements. An object outside the grouping keeps the generic name behavior,
// so an empty name comes back as the empty string rather than NULL. This pins
// the production guard (VpiIsAtomicStmtType) to the atomic statement case -
// without it, the rule would wrongly nullify empty names for every object kind.
TEST_F(AtomicStatement, EmptyNameNullingDoesNotApplyToNonAtomicObjects) {
  VpiObject non_stmt;
  non_stmt.type = vpiModule;  // not an atomic statement
  non_stmt.name = "";         // empty, same as the unlabeled case above
  const char* result = vpi_get_str(vpiName, VpiHandleOf(&non_stmt));
  ASSERT_NE(result, nullptr);
  EXPECT_STREQ(result, "");
}

// §37.60 draws twenty-eight members inside the atomic stmt class, and drawing
// them separately is a claim that they are separate: a vpi_get(vpiType) on a
// statement reports one of them, and two members sharing a constant leave that
// report unable to say which one it found. Annex M is what numbers them, and it
// gives an immediate assume 694 and an immediate cover 695 -- the 666 and 667
// they carried are vpiReturn's and vpiAnyPattern's, so an immediate assume read
// as a return statement and an immediate cover as a case-item any-pattern.
TEST_F(AtomicStatement, TheMembersOfTheClassHaveConstantsOfTheirOwn) {
  EXPECT_EQ(vpiImmediateAssert, 665);
  EXPECT_EQ(vpiImmediateAssume, 694);
  EXPECT_EQ(vpiImmediateCover, 695);
  EXPECT_EQ(vpiReturnStmt, 691);

  // The three the collisions were with, which the class draws elsewhere or not
  // at all: a return statement is its own member, while vpiReturn and
  // vpiAnyPattern are not statements.
  EXPECT_NE(vpiImmediateAssume, vpiReturn);
  EXPECT_NE(vpiImmediateCover, vpiAnyPattern);
  EXPECT_NE(vpiImmediateAssume, vpiReturnStmt);
}

// The tf call class drawn inside atomic stmt holds the three function call
// kinds as well as the task calls (§37.42), and §37.59 draws the same three in
// expr: a function call is an atomic statement where it was written as one and
// an expression everywhere else (#5034).
TEST_F(AtomicStatement, AFunctionCallWrittenAsAStatementIsOne) {
  for (int type : {vpiFuncCall, vpiMethodFuncCall, vpiSysFuncCall}) {
    VpiObject call;
    call.type = type;
    EXPECT_FALSE(VpiIsAtomicStmtObject(&call)) << type;
    EXPECT_TRUE(VpiIsExprObject(&call)) << type;
    call.written_as_stmt = true;
    EXPECT_TRUE(VpiIsAtomicStmtObject(&call)) << type;
    EXPECT_FALSE(VpiIsExprObject(&call)) << type;
  }
}

// So a loop whose body is a call statement and whose condition is a call
// reaches each through its own relation, the body standing first here as a
// do-while writes it.
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

// An if-else whose condition and both branches are calls reaches its else
// branch as the second of the two call statements.
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

// A case item's match expressions are its calls that are expressions, the
// call statement it branches to being none of them.
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

// -----------------------------------------------------------------------------
// The atomic statements of a run, built from the elaborated design rather than
// by hand.
// -----------------------------------------------------------------------------

class AtomicStatementsOfARun : public VpiDesignRun {
 protected:
  // The first object of `type` `ref` reaches, null for none.
  static vpiHandle First(int type, vpiHandle ref) {
    vpiHandle it = vpi_iterate(type, ref);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

// The label property: a labeled statement reports its label through vpiName.
TEST_F(AtomicStatementsOfARun, ALabeledStatementReportsItsLabel) {
  Run("module top; event e; initial trig: -> e; endmodule\n");
  vpiHandle stmt = First(vpiEventStmt, By("top.trig"));
  ASSERT_NE(stmt, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, stmt), "trig");
}

// An unlabeled statement has no label to report.
TEST_F(AtomicStatementsOfARun, AnUnlabeledStatementReportsNoLabel) {
  Run("module top; event e; initial -> e; endmodule\n");
  vpiHandle stmt = First(vpiEventStmt, By("top"));
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, stmt), nullptr);
}

// A null statement is an object of the run, the body of the procedure that
// writes it.
TEST_F(AtomicStatementsOfARun, ANullStatementIsAnObjectOfTheRun) {
  Run("module top; initial ; endmodule\n");
  vpiHandle proc = First(vpiProcess, By("top"));
  ASSERT_NE(proc, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, proc);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiNullStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, body)), VpiObjectOf(proc));
}

// A break and a continue are objects of the run, standing in the block or the
// if statement that holds them and running in the procedure.
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

// -----------------------------------------------------------------------------
// The objects a statement reaches, filled straight from the statement the
// parser hands over, in shapes no source run builds.
// -----------------------------------------------------------------------------

// Builds each object in `made_`. An identifier stands as an object of its
// name, any other expression as none, as one the model leaves out would, and
// a statement the filled one holds as none.
class StatementFill : public ::testing::Test {
 protected:
  // `expr` made an identifier written `text`.
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
      [](const Expr*) { return vpiIntVar; }};
};

// §37.64 detail 1: only an assignment whose right side is an operation over
// its own left side is an operator assignment. One missing its right side, or
// missing its left side under an operation whose left operand is missing
// too, is a plain one.
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

// §37.64 with §37.68: an intra-assignment delay the model leaves out still
// gives the assignment its delay control, one reaching no delay.
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

// §37.65: an event control whose list holds an event the model leaves out - a
// sequence (§9.4.2.4), the edge keyword, or an edge or an iff over an
// expression not modelled - reaches no condition, rather than one standing
// for the other events alone.
TEST_F(StatementFill, AnEventLeftOutLeavesTheControlNoCondition) {
  Expr clk;
  Name(clk, "clk");
  Expr one;
  one.kind = ExprKind::kIntegerLiteral;
  EventExpr modelled;
  modelled.signal = &clk;
  EventExpr sequence;
  sequence.signal = &clk;
  sequence.is_sequence_event = true;
  EventExpr edge;
  edge.signal = &clk;
  edge.edge = Edge::kEdge;
  EventExpr posedge;
  posedge.signal = &one;
  posedge.edge = Edge::kPosedge;
  EventExpr guarded;
  guarded.signal = &clk;
  guarded.iff_condition = &one;
  const std::vector<EventExpr> kLeftOut = {sequence, edge, posedge, guarded};
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

// §37.72: a casex reports vpiCaseX and a casez vpiCaseZ, and a case matches
// (§12.6.1) the tagged qualifier.
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

// §37.74 with §37.12 detail 2: a for statement whose header initializes
// nothing declares no loop variable.
TEST_F(StatementFill, AForInitializingNothingDeclaresNoVariable) {
  Stmt stmt;
  stmt.kind = StmtKind::kFor;
  VpiObject loop;
  loop.type = vpiFor;
  loop.local_var_decls = true;
  VpiFillStmt(&loop, stmt, with_);
  EXPECT_FALSE(loop.local_var_decls);
}

// §37.77 with §9.6.2: a disable reaches no target where it writes no
// hierarchical name - none, a literal, a member access missing its member,
// or one off an expression that is no name - though the named block around it
// answers to the name the expression ends in, nor where its name reaches only
// an object no disable stops, such as a variable.
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
  const auto kTarget = [this, &block](Expr* name) {
    Stmt stmt;
    stmt.kind = StmtKind::kDisable;
    stmt.expr = name;
    VpiObject disable;
    disable.type = vpiDisable;
    disable.parent = &block;
    VpiFillStmt(&disable, stmt, with_);
    return disable.disable_target;
  };
  EXPECT_EQ(kTarget(&b), &block);
  for (Expr* name :
       std::vector<Expr*>{nullptr, &literal, &no_member, &off_literal, &x}) {
    EXPECT_EQ(kTarget(name), nullptr);
  }
}

// §37.50: a cover statement embedded in procedural code is a concurrent
// cover; written otherwise it is an immediate one (§37.55).
TEST(StatementKind, AProceduralConcurrentCoverIsACover) {
  Stmt stmt;
  stmt.kind = StmtKind::kCoverImmediate;
  EXPECT_EQ(VpiBuiltStmtKind(stmt), vpiImmediateCover);
  stmt.is_procedural_concurrent = true;
  EXPECT_EQ(VpiBuiltStmtKind(stmt), vpiCover);
}

// §37.52: a spec is made wherever the parser read a property for it - a tree
// of operators, a sequence or a Boolean - and none where it read none.
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

// §37.52 with §16.12.3: the property expr of a negated Boolean property is
// the not operation over the Boolean.
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
