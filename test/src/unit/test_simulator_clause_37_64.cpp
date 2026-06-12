#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.64 Assignment: the object model diagram draws an "assignment" object with a
// vpiLhs expression, a vpiRhs expression (or interface expression), an int
// vpiOpType property, a bool vpiBlocking property, and delay/event/repeat control
// edges. The clause's sole numbered Detail governs vpiOpType: a normal assignment
// (blocking "=" or nonblocking "<=") reports vpiAssignmentOp, while an assignment
// operator reports the operator combined with the assignment as described in
// 11.4.1 (for example "+=" reports vpiAddOp). These tests observe the production
// code that computes that value (VpiAssignmentOpType) and confirm an assignment
// object carrying the computed value surfaces it through the public
// vpi_get(vpiOpType) dispatch path.

// The fixture installs a context so the public vpi_get entry point runs its real
// dispatch over the test objects.
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

// D1: each assignment operator reports the operator combined with the assignment,
// following the 11.4.1 correspondence - "+=" is the worked example, the rest cover
// the full set of compound operators.
TEST_F(Assignment, AssignmentOperatorsReportTheCombinedOperator) {
  EXPECT_EQ(VpiAssignmentOpType("+="), vpiAddOp);  // the clause's worked example
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

// D1 end to end: an assignment object whose op_type was computed by the production
// rule surfaces that operator through the public vpi_get(vpiOpType) dispatch. A
// normal assignment reports vpiAssignmentOp; a "+=" assignment reports vpiAddOp.
TEST_F(Assignment, AssignmentObjectReportsComputedOpTypeThroughDispatch) {
  VpiObject normal;
  normal.type = vpiAssignment;
  normal.op_type = VpiAssignmentOpType("<=");
  EXPECT_EQ(vpi_get(vpiOpType, &normal), vpiAssignmentOp);

  VpiObject compound;
  compound.type = vpiAssignment;
  compound.op_type = VpiAssignmentOpType("+=");
  EXPECT_EQ(vpi_get(vpiOpType, &compound), vpiAddOp);
}

}  // namespace
}  // namespace delta
