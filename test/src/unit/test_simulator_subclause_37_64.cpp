#include <gtest/gtest.h>

#include <string>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.64 Assignment: the object model diagram draws an "assignment" object with
// a vpiLhs expression, a vpiRhs expression (or interface expression), an int
// vpiOpType property, a bool vpiBlocking property, and delay/event/repeat
// control edges. The clause's sole numbered Detail governs vpiOpType: a normal
// assignment (blocking "=" or nonblocking "<=") reports vpiAssignmentOp, while
// an assignment operator reports the operator combined with the assignment as
// described in 11.4.1 (for example "+=" reports vpiAddOp). These tests observe
// the production code that computes that value (VpiAssignmentOpType) and
// confirm an assignment object carrying the computed value surfaces it through
// the public vpi_get(vpiOpType) dispatch path.

// The fixture installs a context so the public vpi_get entry point runs its
// real dispatch over the test objects.
class Assignment : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1: the normal blocking "=" and nonblocking "<=" forms are both ordinary
// assignments and report vpiAssignmentOp.
TEST_F(Assignment, NormalAssignmentsReportVpiAssignmentOp) {
  EXPECT_EQ(VpiAssignmentOpType("="), vpiAssignmentOp);
  EXPECT_EQ(VpiAssignmentOpType("<="), vpiAssignmentOp);
}

// D1: each assignment operator reports the operator combined with the
// assignment, following the 11.4.1 correspondence - "+=" is the worked example,
// the rest cover the full set of compound operators.
TEST_F(Assignment, AssignmentOperatorsReportTheCombinedOperator) {
  EXPECT_EQ(VpiAssignmentOpType("+="),
            vpiAddOp);  // the clause's worked example
  EXPECT_EQ(VpiAssignmentOpType("-="), vpiSubOp);
  EXPECT_EQ(VpiAssignmentOpType("*="), vpiMultOp);
  EXPECT_EQ(VpiAssignmentOpType("/="), vpiDivOp);
  EXPECT_EQ(VpiAssignmentOpType("%="), vpiModOp);
  EXPECT_EQ(VpiAssignmentOpType("&="), vpiBitAndOp);
  EXPECT_EQ(VpiAssignmentOpType("|="), vpiBitOrOp);
  EXPECT_EQ(VpiAssignmentOpType("^="), vpiBitXorOp);
  EXPECT_EQ(VpiAssignmentOpType("<<="), vpiLShiftOp);
  EXPECT_EQ(VpiAssignmentOpType(">>="), vpiRShiftOp);
  EXPECT_EQ(VpiAssignmentOpType("<<<="), vpiArithLShiftOp);
  EXPECT_EQ(VpiAssignmentOpType(">>>="), vpiArithRShiftOp);
}

// D1 end to end: an assignment object whose op_type was computed by the
// production rule surfaces that operator through the public vpi_get(vpiOpType)
// dispatch. A normal assignment reports vpiAssignmentOp; a "+=" assignment
// reports vpiAddOp.
TEST_F(Assignment, AssignmentObjectReportsComputedOpTypeThroughDispatch) {
  VpiObject normal;
  normal.type = vpiAssignment;
  normal.op_type = VpiAssignmentOpType("<=");
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&normal)), vpiAssignmentOp);

  VpiObject compound;
  compound.type = vpiAssignment;
  compound.op_type = VpiAssignmentOpType("+=");
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&compound)), vpiAddOp);
}

// D1 default (negative) form: the rule recognizes exactly the normal "="/"<="
// forms and the 11.4.1 compound operators. Its default branch documents that
// any other spelling is still treated as an ordinary assignment and reports
// vpiAssignmentOp. A comparison spelling such as "==" - never a valid
// assignment operator - exercises that fall-through, and the computed value
// surfaces unchanged through the public vpi_get(vpiOpType) dispatch.
TEST_F(Assignment, UnrecognizedOperatorSpellingFallsBackToVpiAssignmentOp) {
  EXPECT_EQ(VpiAssignmentOpType("=="), vpiAssignmentOp);

  VpiObject fallback;
  fallback.type = vpiAssignment;
  fallback.op_type = VpiAssignmentOpType("==");
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&fallback)), vpiAssignmentOp);
}

// The assignments of a run: those a design's procedures write, built from the
// elaborated design rather than by hand (#4998).
class AssignmentsOfARun : public VpiDesignRun {
 protected:
  // The statement the first procedure of `scope` runs.
  static vpiHandle BodyOf(const std::string& scope) {
    vpiHandle it = vpi_iterate(vpiProcess, By(scope));
    return it == nullptr ? nullptr : vpi_handle(vpiStmt, vpi_scan(it));
  }

  // The value of the constant `obj` as an integer.
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

// A blocking assignment is an assignment of the run, reaching the variables
// its two sides name, reporting vpiAssignmentOp and blocking.
TEST_F(AssignmentsOfARun, ABlockingAssignmentIsAnObjectOfTheRun) {
  Run("module top; int a, b; initial a = b; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiType, assign), vpiAssignment);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, assign)), VpiObjectOf(By("top.a")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, assign)), VpiObjectOf(By("top.b")));
  EXPECT_EQ(vpi_get(vpiOpType, assign), vpiAssignmentOp);
  EXPECT_EQ(vpi_get(vpiBlocking, assign), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, assign)), VpiObjectOf(By("top")));
}

// A nonblocking assignment does not block, and a literal on its right side is
// a constant of the value written.
TEST_F(AssignmentsOfARun, ANonblockingAssignmentDoesNotBlock) {
  Run("module top; int a; initial a <= 7; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiBlocking, assign), 0);
  EXPECT_EQ(vpi_get(vpiOpType, assign), vpiAssignmentOp);
  vpiHandle rhs = vpi_handle(vpiRhs, assign);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiConstant);
  EXPECT_EQ(IntOf(rhs), 7);
}

// D1: an assignment operator reports the operator it combines with the
// assignment, and its right side is the operand written; an assignment that
// writes the operation out is a normal one whose right side is the operation.
TEST_F(AssignmentsOfARun, AnAssignmentOperatorReportsItsOperator) {
  Run("module top; int a;\n"
      "  initial a += 2;\n"
      "  initial a <<<= 3;\n"
      "  initial a = a + 2;\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle add = vpi_handle(vpiStmt, vpi_scan(it));
  vpiHandle shift = vpi_handle(vpiStmt, vpi_scan(it));
  vpiHandle written = vpi_handle(vpiStmt, vpi_scan(it));
  ASSERT_NE(add, nullptr);
  ASSERT_NE(shift, nullptr);
  ASSERT_NE(written, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, add), vpiAddOp);
  EXPECT_EQ(vpi_get(vpiBlocking, add), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiRhs, add)), 2);
  EXPECT_EQ(vpi_get(vpiOpType, shift), vpiArithLShiftOp);
  EXPECT_EQ(vpi_get(vpiOpType, written), vpiAssignmentOp);
  vpiHandle rhs = vpi_handle(vpiRhs, written);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, rhs), vpiAddOp);
}

// An intra-assignment delay is a delay control the assignment reaches, which
// reaches its delay and, by §37.68 detail 1, no statement.
TEST_F(AssignmentsOfARun, AnIntraAssignmentDelayIsADelayControl) {
  Run("module top; int a, b; initial a = #5 b; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  vpiHandle delay = vpi_handle(vpiDelayControl, assign);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(IntOf(vpi_handle(vpiDelay, delay)), 5);
  EXPECT_EQ(vpi_handle(vpiStmt, delay), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, assign)), VpiObjectOf(By("top.b")));
  EXPECT_EQ(vpi_handle(vpiEventControl, assign), nullptr);
}

// An intra-assignment event control is an event control the assignment
// reaches, written over the posedge operation of the variable it names and,
// by §37.65 detail 1, guarding no statement.
TEST_F(AssignmentsOfARun, AnIntraAssignmentEventIsAnEventControl) {
  Run("module top; bit c; int a, b; initial a <= @(posedge c) b; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  vpiHandle control = vpi_handle(vpiEventControl, assign);
  ASSERT_NE(control, nullptr);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, condition), vpiPosedgeOp);
  vpiHandle operands = vpi_iterate(vpiOperand, condition);
  ASSERT_NE(operands, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(operands)), VpiObjectOf(By("top.c")));
  EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr);
}

// An intra-assignment repeat control (§37.69) reaches its count and the event
// control it repeats, written over the variable it names.
TEST_F(AssignmentsOfARun, AnIntraAssignmentRepeatIsARepeatControl) {
  Run("module top; bit c; int a, b; initial a = repeat (3) @(c) b; "
      "endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  vpiHandle repeat = vpi_handle(vpiRepeatControl, assign);
  ASSERT_NE(repeat, nullptr);
  EXPECT_EQ(IntOf(vpi_handle(vpiExpr, repeat)), 3);
  vpiHandle control = vpi_handle(vpiEventControl, repeat);
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, control)),
            VpiObjectOf(By("top.c")));
}

}  // namespace
}  // namespace delta
