#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_vpi_driver_load_iter.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(NetDriversAndLoads, DriverIterationReachesEveryNetDriverKind) {
  VpiContext ctx;

  VpiObject port;
  port.type = vpiPort;
  VpiObject force;
  force.type = vpiForce;
  VpiObject delay_term;
  delay_term.type = vpiDelayTerm;
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject cont_assign_bit;
  cont_assign_bit.type = vpiContAssignBit;
  VpiObject prim_term;
  prim_term.type = vpiPrimTerm;

  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject unrelated;
  unrelated.type = vpiTypespec;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port,        &force,           &delay_term,
                  &cont_assign, &cont_assign_bit, &prim_term,
                  &assign_stmt, &unrelated};
  force.lhs = &net;
  cont_assign.lhs = &net;
  prim_term.direction = vpiOutput;

  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &net));
  ASSERT_EQ(drivers.size(), 6u);
  EXPECT_TRUE(VpiIterationContains(drivers, &port));
  EXPECT_TRUE(VpiIterationContains(drivers, &force));
  EXPECT_TRUE(VpiIterationContains(drivers, &delay_term));
  EXPECT_TRUE(VpiIterationContains(drivers, &cont_assign));
  EXPECT_TRUE(VpiIterationContains(drivers, &cont_assign_bit));
  EXPECT_TRUE(VpiIterationContains(drivers, &prim_term));
  EXPECT_FALSE(VpiIterationContains(drivers, &assign_stmt));
  EXPECT_FALSE(VpiIterationContains(drivers, &unrelated));
}

TEST(NetDriversAndLoads, LoadIterationReachesNetLoadKindsExcludingPlainPort) {
  VpiContext ctx;

  VpiObject delay_term;
  delay_term.type = vpiDelayTerm;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject force;
  force.type = vpiForce;
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject cont_assign_bit;
  cont_assign_bit.type = vpiContAssignBit;
  VpiObject prim_term;
  prim_term.type = vpiPrimTerm;

  VpiObject driver_port;
  driver_port.type = vpiPort;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&delay_term,      &assign_stmt, &force,      &cont_assign,
                  &cont_assign_bit, &prim_term,   &driver_port};
  force.rhs = &net;
  cont_assign.rhs = &net;
  prim_term.direction = vpiInput;

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  ASSERT_EQ(loads.size(), 6u);
  EXPECT_TRUE(VpiIterationContains(loads, &delay_term));
  EXPECT_TRUE(VpiIterationContains(loads, &assign_stmt));
  EXPECT_TRUE(VpiIterationContains(loads, &force));
  EXPECT_TRUE(VpiIterationContains(loads, &cont_assign));
  EXPECT_TRUE(VpiIterationContains(loads, &cont_assign_bit));
  EXPECT_TRUE(VpiIterationContains(loads, &prim_term));
  EXPECT_FALSE(VpiIterationContains(loads, &driver_port));
}

TEST(NetDriversAndLoads,
     ComplexExpressionInputPortIsLoadAndHighConnReachesExpr) {
  VpiContext ctx;

  VpiObject complex_expr;
  complex_expr.type = vpiOperation;
  complex_expr.op_type = vpiNotOp;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.high_conn = &complex_expr;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  ASSERT_EQ(loads.size(), 1u);
  EXPECT_TRUE(VpiIterationContains(loads, &port));

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiHighConn, VpiHandleOf(&port))),
            &complex_expr);
}

TEST(NetDriversAndLoads, ConcatenationOnInputPortIsNotLoad) {
  VpiContext ctx;

  VpiObject concat;
  concat.type = vpiOperation;
  concat.op_type = vpiConcatOp;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.high_conn = &concat;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_FALSE(VpiIterationContains(loads, &port));
}

TEST(NetDriversAndLoads, MultipleConcatenationOnInputPortIsNotLoad) {
  VpiContext ctx;

  VpiObject multi_concat;
  multi_concat.type = vpiOperation;
  multi_concat.op_type = vpiMultiConcatOp;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.high_conn = &multi_concat;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_FALSE(VpiIterationContains(loads, &port));
}

TEST(NetDriversAndLoads, SimpleReferenceOnInputPortIsNotComplexLoad) {
  VpiContext ctx;

  VpiObject ref;
  ref.type = vpiRefObj;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.high_conn = &ref;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_FALSE(VpiIterationContains(loads, &port));
}

TEST(NetDriversAndLoads, ComplexExpressionOnOutputPortIsNotLoad) {
  VpiContext ctx;

  VpiObject complex_expr;
  complex_expr.type = vpiOperation;
  complex_expr.op_type = vpiNotOp;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiOutput;
  port.high_conn = &complex_expr;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_FALSE(VpiIterationContains(loads, &port));
}

TEST(NetDriversAndLoads, InputPortWithoutHighConnectionIsNotLoad) {
  VpiContext ctx;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;

  VpiObject force;
  force.type = vpiForce;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port, &force};
  force.rhs = &net;

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_TRUE(VpiIterationContains(loads, &force));
  EXPECT_FALSE(VpiIterationContains(loads, &port));
}

TEST(NetDriversAndLoads, DriverIterationReachesAPortBit) {
  VpiContext ctx;

  VpiObject port_bit;
  port_bit.type = vpiPortBit;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;

  VpiObject net;
  net.type = kVpiNet;
  net.children = {&port_bit, &assign_stmt};

  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &net));
  ASSERT_EQ(drivers.size(), 1u);
  EXPECT_TRUE(VpiIterationContains(drivers, &port_bit));
}

TEST(NetDriversAndLoads, LoadIterationReachesAPortBitWithAComplexExpression) {
  VpiContext ctx;

  VpiObject expr;
  expr.type = vpiOperation;
  expr.op_type = vpiNotOp;

  VpiObject port_bit;
  port_bit.type = vpiPortBit;
  port_bit.direction = vpiInput;
  port_bit.high_conn = &expr;

  VpiObject plain_bit;
  plain_bit.type = vpiPortBit;
  plain_bit.direction = vpiInput;

  VpiObject net;
  net.type = kVpiNet;
  net.children = {&port_bit, &plain_bit};

  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  ASSERT_EQ(loads.size(), 1u);
  EXPECT_TRUE(VpiIterationContains(loads, &port_bit));

  EXPECT_EQ(ctx.Handle(vpiHighConn, loads[0]), &expr);
}

TEST(NetDriversAndLoads, ALoadIterationPassesOverTheNetsBits) {
  VpiContext ctx;
  VpiObject bit;
  bit.type = vpiNetBit;
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject net;
  net.type = vpiNet;
  net.children = {&bit, &cont_assign};
  cont_assign.rhs = &net;
  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  ASSERT_EQ(loads.size(), 1u);
  EXPECT_EQ(loads[0], &cont_assign);
}

TEST(NetDriversAndLoads, ANetBitReachesItsNetDriversAndLoads) {
  VpiContext ctx;
  VpiObject force;
  force.type = vpiForce;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject bit;
  bit.type = vpiNetBit;
  bit.children = {&force, &assign_stmt};
  force.lhs = &bit;
  force.rhs = &bit;
  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &bit));
  ASSERT_EQ(drivers.size(), 1u);
  EXPECT_EQ(drivers[0], &force);
  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &bit));
  ASSERT_EQ(loads.size(), 2u);
  EXPECT_TRUE(VpiIterationContains(loads, &assign_stmt));
}

TEST(NetDriversAndLoads, ADelayTermHeldByNoDelayDeviceDrivesAndLoads) {
  VpiContext ctx;
  VpiObject holder;
  holder.type = vpiModule;
  VpiObject term;
  term.type = vpiDelayTerm;
  term.parent = &holder;
  VpiObject net;
  net.type = vpiNet;
  net.children = {&term};
  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &net));
  ASSERT_EQ(drivers.size(), 1u);
  EXPECT_EQ(drivers[0], &term);
  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &net));
  ASSERT_EQ(loads.size(), 1u);
  EXPECT_EQ(loads[0], &term);
}

class NetDriversAndLoadsOfARun : public VpiDesignRun {
 protected:
  static bool Holds(const std::vector<int>& kinds, int kind) {
    return std::ranges::find(kinds, kind) != kinds.end();
  }
};

TEST_F(NetDriversAndLoadsOfARun, AContinuousAssignmentDrivesOrLoadsByItsSide) {
  Run("module top; wire w, x, i; wire [1:0] v, u;\n"
      "  assign w = x;\n"
      "  assign v = {u[i], v[0]};\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiDriver, By("top.w")), vpiContAssign));
  EXPECT_FALSE(Holds(KindsOf(vpiLoad, By("top.w")), vpiContAssign));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.x")), vpiContAssign));
  EXPECT_FALSE(Holds(KindsOf(vpiDriver, By("top.x")), vpiContAssign));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.i")), vpiContAssign));
  EXPECT_FALSE(Holds(KindsOf(vpiDriver, By("top.u")), vpiContAssign));
  EXPECT_TRUE(Holds(KindsOf(vpiDriver, By("top.v")), vpiContAssign));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.v")), vpiContAssign));
}

TEST_F(NetDriversAndLoadsOfARun, PrimTermsForcesAndComplexPortsDriveAndLoad) {
  Run("module ram(input a, input b); endmodule\n"
      "module top; wire y, a, b, trinet, n, m;\n"
      "  and g(y, a, b);\n"
      "  ram r0(a, !trinet);\n"
      "  initial force n = m;\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiDriver, By("top.y")), vpiPrimTerm));
  EXPECT_FALSE(Holds(KindsOf(vpiLoad, By("top.y")), vpiPrimTerm));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.a")), vpiPrimTerm));
  EXPECT_FALSE(Holds(KindsOf(vpiDriver, By("top.a")), vpiPrimTerm));
  EXPECT_TRUE(Holds(KindsOf(vpiDriver, By("top.n")), vpiForce));
  EXPECT_FALSE(Holds(KindsOf(vpiLoad, By("top.n")), vpiForce));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.m")), vpiForce));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.trinet")), vpiPort));
  EXPECT_FALSE(Holds(KindsOf(vpiDriver, By("top.trinet")), vpiPort));
}

TEST_F(NetDriversAndLoadsOfARun, AForceReachesTheNetsThroughOperandsAndBits) {
  Run("module top; wire n, m, k; wire [1:0] v;\n"
      "  initial begin force n = m & k & 1'b1; force v[1] = m & m; end\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.k")), vpiForce));
  const std::vector<int> kLoadsOfM = KindsOf(vpiLoad, By("top.m"));
  EXPECT_EQ(std::ranges::count(kLoadsOfM, vpiForce), 2);
  EXPECT_TRUE(Holds(KindsOf(vpiDriver, By("top.v")), vpiForce));
  EXPECT_FALSE(Holds(KindsOf(vpiLoad, By("top.v")), vpiForce));
}

TEST_F(NetDriversAndLoadsOfARun, ASwitchChannelTermDrivesAndLoadsItsNet) {
  Run("module top; wire a, b, c;\n"
      "  tranif1 g(a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiDriver, By("top.a")), vpiPrimTerm));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.a")), vpiPrimTerm));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.c")), vpiPrimTerm));
  EXPECT_FALSE(Holds(KindsOf(vpiDriver, By("top.c")), vpiPrimTerm));
}

TEST_F(NetDriversAndLoadsOfARun, AContinuousAssignmentLoadsTheNetsACallReads) {
  Run("module top;\n"
      "  function automatic logic f(logic a); return a; endfunction\n"
      "  wire w; wire [1:0] v; logic o, p;\n"
      "  assign o = f(w);\n"
      "  assign p = f(v[1]);\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.w")), vpiContAssign));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, vpi_handle_by_index(By("top.v"), 1)),
                    vpiContAssign));
}

TEST_F(NetDriversAndLoadsOfARun, AForceLoadsTheNetsItsIndexAndArgumentRead) {
  Run("module top;\n"
      "  function automatic logic f(logic a); return a; endfunction\n"
      "  logic [3:0] v; logic o1, o2; wire n, w;\n"
      "  initial begin force o1 = v[n]; force o2 = f(w); end\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.n")), vpiForce));
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.w")), vpiForce));
}

TEST_F(NetDriversAndLoadsOfARun, AProceduralAssignLoadsTheNetItReads) {
  Run("module top; logic q; wire n;\n"
      "  initial assign q = n;\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.n")), vpiAssignStmt));
  EXPECT_FALSE(Holds(KindsOf(vpiDriver, By("top.n")), vpiAssignStmt));
}

}  // namespace
}  // namespace delta
