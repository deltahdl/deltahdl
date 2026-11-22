#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class AssignDeassignForceRelease : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(AssignDeassignForceRelease, AssignStatementReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  assign_stmt.lhs = &target;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&assign_stmt))),
            &target);
}

TEST_F(AssignDeassignForceRelease, AssignStatementReachesRhsValue) {
  VpiObject value;
  value.type = vpiOperation;

  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  assign_stmt.rhs = &value;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&assign_stmt))), &value);
}

TEST_F(AssignDeassignForceRelease, ForceReachesRhsValueDistinctFromLhs) {
  VpiObject target;
  target.type = vpiRefObj;
  VpiObject value;
  value.type = vpiOperation;

  VpiObject force;
  force.type = vpiForce;
  force.lhs = &target;
  force.rhs = &value;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&force))), &value);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&force))), &target);
}

TEST_F(AssignDeassignForceRelease, DeassignReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject deassign;
  deassign.type = vpiDeassign;
  deassign.lhs = &target;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&deassign))), &target);
}

TEST_F(AssignDeassignForceRelease, ReleaseReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject release;
  release.type = vpiRelease;
  release.lhs = &target;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&release))), &target);
}

TEST_F(AssignDeassignForceRelease, DeassignAndReleaseDrawNoRhsEdge) {
  VpiObject value;
  value.type = vpiOperation;

  VpiObject deassign;
  deassign.type = vpiDeassign;
  deassign.rhs = &value;

  VpiObject release;
  release.type = vpiRelease;
  release.rhs = &value;

  EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&deassign)), nullptr);
  EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&release)), nullptr);
}

TEST_F(AssignDeassignForceRelease, LhsRelationIsScopedToTheAssignmentFamily) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject not_in_family;
  not_in_family.type = vpiBegin;
  not_in_family.lhs = &target;

  EXPECT_EQ(vpi_handle(vpiLhs, VpiHandleOf(&not_in_family)), nullptr);
}

TEST_F(AssignDeassignForceRelease, EachExpressionKindIsReachedByBothEdges) {
  for (int expr_kind : {vpiOperation, vpiConstant, vpiRefObj, vpiFuncCall,
                        vpiParameter, vpiBitSelect, vpiPartSelect}) {
    VpiObject target;
    target.type = expr_kind;
    VpiObject value;
    value.type = expr_kind;

    VpiObject force;
    force.type = vpiForce;
    force.lhs = &target;
    force.rhs = &value;

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&force))), &target)
        << "kind " << expr_kind;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&force))), &value)
        << "kind " << expr_kind;
  }
}

TEST_F(AssignDeassignForceRelease, EachKindReportsNoExpressionWhenNoneIsSet) {
  VpiObject stray;
  stray.type = vpiRefObj;

  for (int stmt_kind : {vpiAssignStmt, vpiForce, vpiDeassign, vpiRelease}) {
    VpiObject stmt;
    stmt.type = stmt_kind;
    stmt.children = {&stray};

    EXPECT_EQ(vpi_handle(vpiLhs, VpiHandleOf(&stmt)), nullptr)
        << "kind " << stmt_kind;
  }

  for (int stmt_kind : {vpiAssignStmt, vpiForce}) {
    VpiObject stmt;
    stmt.type = stmt_kind;
    stmt.children = {&stray};

    EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&stmt)), nullptr)
        << "kind " << stmt_kind;
  }
}

class ProceduralContinuousAssignmentsOfARun : public VpiDesignRun {
 protected:
  std::vector<vpiHandle> StatementsOfTheInitial(const std::string& body) {
    Run("module top; logic r, a, b; wire w1, w2; wire [3:0] w;\n"
        "  function logic f(logic x); return x; endfunction\n"
        "  initial begin\n" +
        body + "  end\nendmodule\n");
    vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
    if (procs == nullptr) return {};
    return ObjectsOf(vpiStmt, vpi_handle(vpiStmt, vpi_scan(procs)));
  }

  static void ExpectConcatOf(vpiHandle concat, const char* first,
                             const char* second) {
    ASSERT_NE(concat, nullptr);
    EXPECT_EQ(vpi_get(vpiType, concat), vpiOperation);
    EXPECT_EQ(vpi_get(vpiOpType, concat), vpiConcatOp);
    EXPECT_EQ(NamesOf(vpiOperand, concat),
              (std::vector<std::string>{first, second}));
  }

  static void ExpectSelectOfW(vpiHandle select, int kind) {
    ASSERT_NE(select, nullptr);
    EXPECT_EQ(vpi_get(vpiType, select), kind);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, select)),
              VpiObjectOf(By("top.w")));
  }

  static vpiHandle FirstOf(int type, vpiHandle ref) {
    vpiHandle it = vpi_iterate(type, ref);
    return it == nullptr ? nullptr : vpi_scan(it);
  }

  static vpiHandle InnerOf(vpiHandle stmt) {
    const int kKind = vpi_get(vpiType, stmt);
    if (kKind == vpiFork) return FirstOf(vpiStmt, stmt);
    if (kKind == vpiCase) stmt = FirstOf(vpiCaseItem, stmt);
    return stmt == nullptr ? nullptr : vpi_handle(vpiStmt, stmt);
  }

  static vpiHandle FourIn(vpiHandle stmt) {
    while (stmt != nullptr && vpi_get(vpiType, stmt) != vpiBegin) {
      stmt = InnerOf(stmt);
    }
    return stmt;
  }
};

TEST_F(ProceduralContinuousAssignmentsOfARun, EachIsAnObjectOfTheRun) {
  Run("module top; logic r; wire w;\n"
      "  initial begin assign r = 1; deassign r; force w = 1; release w; end\n"
      "endmodule\n");
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  vpiHandle block = vpi_handle(vpiStmt, vpi_scan(procs));
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(
      KindsOf(vpiStmt, block),
      (std::vector<int>{vpiAssignStmt, vpiDeassign, vpiForce, vpiRelease}));
  vpiHandle it = vpi_iterate(vpiStmt, block);
  ASSERT_NE(it, nullptr);
  vpiHandle assign = vpi_scan(it);
  vpiHandle deassign = vpi_scan(it);
  vpiHandle force = vpi_scan(it);
  vpiHandle release = vpi_scan(it);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, assign)), VpiObjectOf(By("top.r")));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiRhs, assign)), vpiConstant);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, deassign)),
            VpiObjectOf(By("top.r")));
  EXPECT_EQ(vpi_handle(vpiRhs, deassign), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, force)), VpiObjectOf(By("top.w")));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiRhs, force)), vpiConstant);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, release)), VpiObjectOf(By("top.w")));
  EXPECT_EQ(vpi_handle(vpiRhs, release), nullptr);
}

TEST_F(ProceduralContinuousAssignmentsOfARun,
       AForceAndAReleaseOfAVariableReachItAsTheirTarget) {
  const std::vector<vpiHandle> kStmts =
      StatementsOfTheInitial("force r = 1; release r;\n");
  ASSERT_EQ(kStmts.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kStmts[0]), vpiForce);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, kStmts[0])),
            VpiObjectOf(By("top.r")));
  EXPECT_EQ(vpi_get(vpiType, kStmts[1]), vpiRelease);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, kStmts[1])),
            VpiObjectOf(By("top.r")));
  EXPECT_EQ(vpi_handle(vpiRhs, kStmts[1]), nullptr);
}

TEST_F(ProceduralContinuousAssignmentsOfARun,
       AConcatenationTargetIsAConcatenationOfItsMembers) {
  const std::vector<vpiHandle> kStmts = StatementsOfTheInitial(
      "assign {a, b} = 2'b10; deassign {a, b};\n"
      "force {w1, w2} = 2'b01; release {w1, w2};\n");
  ASSERT_EQ(kStmts.size(), 4U);
  ExpectConcatOf(vpi_handle(vpiLhs, kStmts[0]), "a", "b");
  ExpectConcatOf(vpi_handle(vpiLhs, kStmts[1]), "a", "b");
  ExpectConcatOf(vpi_handle(vpiLhs, kStmts[2]), "w1", "w2");
  ExpectConcatOf(vpi_handle(vpiLhs, kStmts[3]), "w1", "w2");
  EXPECT_EQ(vpi_handle(vpiRhs, kStmts[1]), nullptr);
  EXPECT_EQ(vpi_handle(vpiRhs, kStmts[3]), nullptr);
}

TEST_F(ProceduralContinuousAssignmentsOfARun,
       ASelectTargetIsTheSelectOfItsNet) {
  const std::vector<vpiHandle> kStmts = StatementsOfTheInitial(
      "force w[1] = 1; release w[1];\n"
      "force w[3:2] = 2'b11; release w[3:2];\n");
  ASSERT_EQ(kStmts.size(), 4U);
  ExpectSelectOfW(vpi_handle(vpiLhs, kStmts[0]), vpiNetBit);
  ExpectSelectOfW(vpi_handle(vpiLhs, kStmts[1]), vpiNetBit);
  ExpectSelectOfW(vpi_handle(vpiLhs, kStmts[2]), vpiPartSelect);
  ExpectSelectOfW(vpi_handle(vpiLhs, kStmts[3]), vpiPartSelect);
  EXPECT_EQ(vpi_handle(vpiRhs, kStmts[1]), nullptr);
  EXPECT_EQ(vpi_handle(vpiRhs, kStmts[3]), nullptr);
}

TEST_F(ProceduralContinuousAssignmentsOfARun, EachKindOfValueIsReached) {
  const std::vector<vpiHandle> kStmts = StatementsOfTheInitial(
      "assign r = a & b; force w1 = w2; assign r = f(a);\n"
      "force w1 = w[0]; force w1 = w[2:1];\n");
  ASSERT_EQ(kStmts.size(), 5U);
  vpiHandle op = vpi_handle(vpiRhs, kStmts[0]);
  ASSERT_NE(op, nullptr);
  EXPECT_EQ(vpi_get(vpiType, op), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, op), vpiBitAndOp);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, kStmts[1])),
            VpiObjectOf(By("top.w2")));
  vpiHandle call = vpi_handle(vpiRhs, kStmts[2]);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "f");
  ExpectSelectOfW(vpi_handle(vpiRhs, kStmts[3]), vpiNetBit);
  ExpectSelectOfW(vpi_handle(vpiRhs, kStmts[4]), vpiPartSelect);
}

TEST_F(ProceduralContinuousAssignmentsOfARun, EachPlaceBuildsAllFourKinds) {
  const std::string kFour =
      " begin assign r = 1; deassign r; force w = 1; release w; end ";
  const std::string kDecls = " logic r; wire w; ";
  Run("interface ifc;" + kDecls + "initial" + kFour + "endinterface\n" +
      "program prg;" + kDecls + "initial" + kFour + "endprogram\n" +
      "module top;" + kDecls + "event e; ifc i0(); prg p0();\n" +
      "  always @(e)" + kFour + "\n  final" + kFour + "\n  initial if (1)" +
      kFour + "\n  initial case (1) 1:" + kFour +
      "endcase\n  initial repeat (1)" + kFour + "\n  initial fork" + kFour +
      "join\n  task tk;" + kFour + "endtask\nendmodule\n");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 6U);
  const std::vector<std::pair<const char*, vpiHandle>> kPlaces{
      {"always", kProcs[0]},
      {"final", kProcs[1]},
      {"if", kProcs[2]},
      {"case", kProcs[3]},
      {"repeat", kProcs[4]},
      {"fork", kProcs[5]},
      {"task", Named(vpiTask, By("top"), "tk")},
      {"interface", SoleProcessOf("top.i0")},
      {"program", SoleProcessOf("top.p0")}};
  for (const auto& [where, place] : kPlaces) {
    ASSERT_NE(place, nullptr) << where;
    vpiHandle block = FourIn(vpi_handle(vpiStmt, place));
    ASSERT_NE(block, nullptr) << where;
    EXPECT_EQ(
        KindsOf(vpiStmt, block),
        (std::vector<int>{vpiAssignStmt, vpiDeassign, vpiForce, vpiRelease}))
        << where;
  }
}

}  // namespace
}  // namespace delta
