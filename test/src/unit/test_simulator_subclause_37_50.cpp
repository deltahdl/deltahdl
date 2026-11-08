#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(ConcurrentAssertionModel, ConcurrentAssertionTypeCoversTheFourDirectives) {
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiAssert));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiAssume));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiCover));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiRestrict));

  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiImmediateAssert));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiPropertyInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiModule));
}

TEST(ConcurrentAssertionModel, PropertyRelationTargetKinds) {
  EXPECT_TRUE(VpiIsConcurrentAssertionPropertyType(vpiPropertyInst));
  EXPECT_TRUE(VpiIsConcurrentAssertionPropertyType(vpiPropertySpec));

  EXPECT_FALSE(VpiIsConcurrentAssertionPropertyType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionPropertyType(vpiOperation));
}

TEST(ConcurrentAssertionModel, AssertionReachesItsProperty) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  assertion.children = {&spec};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&assertion), &spec);

  VpiObject with_inst;
  with_inst.type = vpiAssume;
  VpiObject inst;
  inst.type = vpiPropertyInst;
  with_inst.children = {&inst};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&with_inst), &inst);

  VpiObject bare;
  bare.type = vpiCover;
  EXPECT_EQ(VpiConcurrentAssertionProperty(&bare), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionProperty(nullptr), nullptr);
}

TEST(ConcurrentAssertionModel, ClockingEventIsTheActualEventForBothForms) {
  VpiContext ctx;

  VpiObject explicit_clk;
  explicit_clk.type = vpiAssert;
  VpiObject ev0;
  ev0.type = vpiOperation;
  explicit_clk.clocking_event = &ev0;
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&explicit_clk), &ev0);
  EXPECT_EQ(ctx.Get(vpiIsClockInferred, &explicit_clk), 0);

  VpiObject inferred_clk;
  inferred_clk.type = vpiAssert;
  inferred_clk.clock_inferred = true;
  VpiObject ev1;
  ev1.type = vpiOperation;
  inferred_clk.clocking_event = &ev1;
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&inferred_clk), &ev1);
  EXPECT_EQ(ctx.Get(vpiIsClockInferred, &inferred_clk), 1);
}

TEST(ConcurrentAssertionModel, MissingClockingEventReportsNull) {
  VpiObject assertion;
  assertion.type = vpiAssume;
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&assertion), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(nullptr), nullptr);
}

TEST(ConcurrentAssertionModel, CoverReportsIsCoverSequence) {
  VpiContext ctx;
  VpiObject seq_cover;
  seq_cover.type = vpiCover;
  seq_cover.cover_sequence = true;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &seq_cover), 1);

  VpiObject prop_cover;
  prop_cover.type = vpiCover;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &prop_cover), 0);
}

TEST(ConcurrentAssertionModel, NonCoverReportsIsCoverSequenceFalse) {
  VpiContext ctx;
  VpiObject assertion;
  assertion.type = vpiAssert;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &assertion), 0);

  VpiObject assume_obj;
  assume_obj.type = vpiAssume;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &assume_obj), 0);
}

TEST(ConcurrentAssertionModel, PassStatementPresenceByKind) {
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiAssume));
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiCover));
  EXPECT_FALSE(VpiConcurrentAssertionHasPassStmt(vpiRestrict));
}

TEST(ConcurrentAssertionModel, ElseStatementPresenceByKind) {
  EXPECT_TRUE(VpiConcurrentAssertionHasElseStmt(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionHasElseStmt(vpiAssume));
  EXPECT_FALSE(VpiConcurrentAssertionHasElseStmt(vpiCover));
  EXPECT_FALSE(VpiConcurrentAssertionHasElseStmt(vpiRestrict));
}

TEST(ConcurrentAssertionModel, AssertReachesPassAndElseStatements) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject pass;
  pass.type = vpiAssignment;
  VpiObject els;
  els.type = vpiAssignment;
  assertion.children = {&pass, &els};
  assertion.else_stmt = &els;
  EXPECT_EQ(VpiConcurrentAssertionStmt(&assertion), &pass);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&assertion), &els);

  VpiObject pass_only;
  pass_only.type = vpiCover;
  VpiObject p2;
  p2.type = vpiAssignment;
  VpiObject p3;
  p3.type = vpiAssignment;
  pass_only.children = {&p2, &p3};
  EXPECT_EQ(VpiConcurrentAssertionStmt(&pass_only), &p2);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&pass_only), nullptr);

  VpiObject fail_only;
  fail_only.type = vpiAssume;
  VpiObject f;
  f.type = vpiAssignment;
  fail_only.children = {&f};
  fail_only.else_stmt = &f;
  EXPECT_EQ(VpiConcurrentAssertionStmt(&fail_only), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&fail_only), &f);

  EXPECT_EQ(VpiConcurrentAssertionStmt(nullptr), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(nullptr), nullptr);
}

TEST(ConcurrentAssertionModel, RestrictIsNotSimulated) {
  EXPECT_FALSE(VpiConcurrentAssertionIsSimulated(vpiRestrict));

  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiAssume));
  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiCover));

  EXPECT_FALSE(VpiConcurrentAssertionIsSimulated(vpiModule));
}

TEST(ConcurrentAssertionModel, AssertionReportsNameAndFullName) {
  VpiContext ctx;
  std::string name = "req_ack";
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.name = name;
  assertion.full_name = "top.u_dut.req_ack";

  EXPECT_STREQ(ctx.GetStr(vpiName, &assertion), "req_ack");
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &assertion), "top.u_dut.req_ack");
}

TEST(ConcurrentAssertionModel, PropertyTraversalSkipsNonPropertyChildren) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&assertion), nullptr);
}

TEST(ConcurrentAssertionModel, ClockingEventIsNoChildOfTheAssertion) {
  VpiObject assertion;
  assertion.type = vpiAssume;
  VpiObject control;
  control.type = vpiEventControl;
  assertion.children = {&control};
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&assertion), nullptr);
}

TEST(ConcurrentAssertionModel, StatementTraversalsSkipNonStatementChildren) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiConcurrentAssertionStmt(&assertion), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&assertion), nullptr);
}

class ConcurrentAssertionsOfARun : public VpiDesignRun {
 protected:
  static std::string NameReached(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? "" : vpi_get_str(vpiName, reached);
  }

  static std::string EdgeOf(vpiHandle event) {
    if (event == nullptr || vpi_get(vpiType, event) != vpiOperation) return "";
    const int kOp = vpi_get(vpiOpType, event);
    vpiHandle operands = vpi_iterate(vpiOperand, event);
    vpiHandle operand = operands == nullptr ? nullptr : vpi_scan(operands);
    if (operand == nullptr) return "";
    const std::string kName = vpi_get_str(vpiName, operand);
    if (kOp == vpiPosedgeOp) return "posedge " + kName;
    return kOp == vpiNegedgeOp ? "negedge " + kName : "";
  }
};

TEST_F(ConcurrentAssertionsOfARun, AnItemReachesBothActions) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a) $display(\"p\");\n"
      "      else $write(\"f\");\n"
      "  c1: cover property (@(posedge clk) a) $display(\"c\");\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  vpiHandle c1 = Named(vpiAssertion, By("top"), "c1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(c1, nullptr);
  EXPECT_EQ(ActionReached(vpiStmt, a1), "$display");
  EXPECT_EQ(ActionReached(vpiElseStmt, a1), "$write");
  EXPECT_EQ(ActionReached(vpiStmt, c1), "$display");
  EXPECT_EQ(ActionReached(vpiElseStmt, c1), "");
}

TEST_F(ConcurrentAssertionsOfARun, AFailActionAloneIsTheElseStatement) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a) else $write(\"f\");\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ActionReached(vpiStmt, a1), "");
  EXPECT_EQ(ActionReached(vpiElseStmt, a1), "$write");
}

TEST_F(ConcurrentAssertionsOfARun, AProceduralAssertionReachesBothActions) {
  Run("module top; logic clk, a;\n"
      "  always @(posedge clk)\n"
      "    p1: assert property (a) $display(\"p\"); else $write(\"f\");\n"
      "endmodule\n");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(ActionReached(vpiStmt, p1), "$display");
  EXPECT_EQ(ActionReached(vpiElseStmt, p1), "$write");
}

TEST_F(ConcurrentAssertionsOfARun, AnAssertionReachesTheClockItWrites) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, a1)), "posedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, a1), 0);
}

TEST_F(ConcurrentAssertionsOfARun, AnInferredClockIsReachedAndReported) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  a1: assert property (a);\n"
      "  always @(posedge clk) p1: assert property (a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, a1)), "negedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, a1), 1);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, p1)), "posedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, p1), 1);
}

TEST_F(ConcurrentAssertionsOfARun, AnAssertionReachesItsPropertySpec) {
  Run("module top; logic clk, rst, a;\n"
      "  a1: assert property (@(posedge clk) disable iff (rst) a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle spec = vpi_handle(vpiProperty, a1);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, spec)), "posedge clk");
  EXPECT_EQ(NameReached(vpiDisableCondition, spec), "rst");
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

TEST_F(ConcurrentAssertionsOfARun, ABareNameIsABooleanPropertySpec) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  a1: assert property (a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle spec = vpi_handle(vpiProperty, a1);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, spec)), "negedge clk");
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

TEST_F(ConcurrentAssertionsOfARun, ARestrictReachesItsClockAndPropertySpec) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  r1: restrict property (@(posedge clk) a);\n"
      "  r2: restrict property (a);\n"
      "endmodule\n");
  vpiHandle r1 = Named(vpiAssertion, By("top"), "r1");
  vpiHandle r2 = Named(vpiAssertion, By("top"), "r2");
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, r1)), "posedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, r1), 0);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, r2)), "negedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, r2), 1);
  vpiHandle spec = vpi_handle(vpiProperty, r1);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

TEST_F(ConcurrentAssertionsOfARun, AGlobalClockIsTheEventItsInstanceResolves) {
  Run("module child(input logic clk, a);\n"
      "  a1: assert property (@$global_clock a);\n"
      "endmodule\n"
      "module rise(input logic clk, a);\n"
      "  global clocking @(posedge clk); endclocking\n"
      "  child c(clk, a);\n"
      "endmodule\n"
      "module fall(input logic clk, a);\n"
      "  global clocking @(negedge clk); endclocking\n"
      "  child c(clk, a);\n"
      "endmodule\n"
      "module top; logic clk, a;\n"
      "  rise u1(clk, a);\n"
      "  fall u2(clk, a);\n"
      "endmodule\n");
  vpiHandle up = Named(vpiAssertion, By("top.u1.c"), "a1");
  vpiHandle down = Named(vpiAssertion, By("top.u2.c"), "a1");
  ASSERT_NE(up, nullptr);
  ASSERT_NE(down, nullptr);
  vpiHandle rising = vpi_handle(vpiClockingEvent, up);
  vpiHandle falling = vpi_handle(vpiClockingEvent, down);
  ASSERT_NE(rising, nullptr);
  ASSERT_NE(falling, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, rising), vpiPosedgeOp);
  EXPECT_EQ(vpi_get(vpiOpType, falling), vpiNegedgeOp);
}

TEST_F(ConcurrentAssertionsOfARun, AProceduralGlobalClockIsTheDeclaredEvent) {
  Run("module top; logic clk, a;\n"
      "  global clocking @(negedge clk); endclocking\n"
      "  always @(posedge clk) p1: assert property (@$global_clock a);\n"
      "endmodule\n");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, p1)), "negedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, p1), 0);
}

TEST(ConcurrentAssertionStmt, ANullHandleOrARestrictHasNoPassStatement) {
  EXPECT_EQ(VpiConcurrentAssertionStmt(nullptr), nullptr);
  VpiObject restrict_property;
  restrict_property.type = vpiRestrict;
  EXPECT_EQ(VpiConcurrentAssertionStmt(&restrict_property), nullptr);
}
}  // namespace
}  // namespace delta
