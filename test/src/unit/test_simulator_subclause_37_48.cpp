#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ClockingBlock : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(ClockingBlock, PrefixReachesVirtualInterfacePrefix) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};

  EXPECT_EQ(VpiClockingBlockPrefix(&block), &vif);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, VpiHandleOf(&block))), &vif);
}

TEST_F(ClockingBlock, PrefixIsNullWhenNotVirtualInterfacePrefixed) {
  VpiObject event_ctrl;
  event_ctrl.type = vpiEventControl;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&event_ctrl};

  EXPECT_EQ(VpiClockingBlockPrefix(&block), nullptr);
  EXPECT_EQ(vpi_handle(vpiPrefix, VpiHandleOf(&block)), nullptr);
}

TEST_F(ClockingBlock, ActualReachesResolvedClockingBlockWhenPrefixHasValue) {
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.actual = &iface;

  VpiObject resolved;
  resolved.type = vpiClockingBlock;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};
  block.actual = &resolved;

  EXPECT_EQ(VpiClockingBlockActual(&block), &resolved);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&block))), &resolved);
}

TEST_F(ClockingBlock, ActualIsNullWhenVirtualInterfacePrefixHasNoValue) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;

  VpiObject resolved;
  resolved.type = vpiClockingBlock;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};
  block.actual = &resolved;

  EXPECT_EQ(VpiClockingBlockActual(&block), nullptr);
  EXPECT_EQ(vpi_handle(vpiActual, VpiHandleOf(&block)), nullptr);
}

TEST_F(ClockingBlock, ActualReachesActualWhenNotVirtualInterfacePrefixed) {
  VpiObject resolved;
  resolved.type = vpiClockingBlock;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.actual = &resolved;

  EXPECT_EQ(VpiClockingBlockActual(&block), &resolved);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&block))), &resolved);
}

TEST_F(ClockingBlock, ActualWithNoRunIsTheBlockAPrefixedBlockWasBuiltWith) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;

  VpiObject resolved;
  resolved.type = vpiClockingBlock;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.prefix = &vif;
  block.actual = &resolved;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&block))), &resolved);
}

TEST_F(ClockingBlock, IODeclExprGroupMembership) {
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiRefObj));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(kVpiNet));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(kVpiReg));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiIntVar));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiStringVar));
  EXPECT_FALSE(VpiIsClockingIODeclExprType(vpiDelayControl));
}

TEST_F(ClockingBlock, IODeclExprReachesNamedRefObj) {
  VpiObject ref;
  ref.type = vpiRefObj;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&ref};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &ref);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &ref);
}

TEST_F(ClockingBlock, IODeclExprIsNullWhenNothingNamed) {
  VpiObject skew;
  skew.type = vpiDelayControl;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&skew};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&io_decl)), nullptr);
}

TEST_F(ClockingBlock, IODeclExprReachesNamedNet) {
  VpiObject skew;
  skew.type = vpiDelayControl;

  VpiObject net;
  net.type = kVpiNet;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&skew, &net};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &net);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &net);
}

TEST_F(ClockingBlock, IODeclExprReachesNamedVariable) {
  VpiObject var;
  var.type = kVpiReg;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&var};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &var);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &var);
}

TEST_F(ClockingBlock, IODeclExprReachesVariablesGrouping) {
  VpiObject var;
  var.type = vpiIntVar;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&var};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &var);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &var);
}

TEST_F(ClockingBlock, ClockingEventReachesEventControl) {
  VpiObject event_ctrl;
  event_ctrl.type = vpiEventControl;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&event_ctrl};

  EXPECT_EQ(VpiClockingBlockClockingEvent(&block), &event_ctrl);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClockingEvent, VpiHandleOf(&block))),
            &event_ctrl);
}

TEST_F(ClockingBlock, ClockingEventIsNullWhenNoEventControl) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};

  EXPECT_EQ(VpiClockingBlockClockingEvent(&block), nullptr);
  EXPECT_EQ(vpi_handle(vpiClockingEvent, VpiHandleOf(&block)), nullptr);
}

TEST_F(ClockingBlock, HelpersGuardOnObjectKind) {
  VpiObject other;
  other.type = vpiModule;

  EXPECT_EQ(VpiClockingBlockPrefix(&other), nullptr);
  EXPECT_EQ(VpiClockingBlockPrefix(nullptr), nullptr);
  EXPECT_EQ(VpiClockingBlockActual(&other), nullptr);
  EXPECT_EQ(VpiClockingBlockActual(nullptr), nullptr);
  EXPECT_EQ(VpiClockingIODeclExpr(&other), nullptr);
  EXPECT_EQ(VpiClockingIODeclExpr(nullptr), nullptr);
  EXPECT_EQ(VpiClockingBlockClockingEvent(&other), nullptr);
  EXPECT_EQ(VpiClockingBlockClockingEvent(nullptr), nullptr);
}

class ClockingBlocksOfARun : public VpiDesignRun {
 protected:
  static vpiHandle ControlOf(const char* name) {
    return vpi_handle(vpiStmt, Named(vpiTaskFunc, By("top"), name));
  }

  static void ExpectBlockPrefixedBy(vpiHandle tf, const char* var_name) {
    ASSERT_NE(tf, nullptr) << var_name;
    vpiHandle control = vpi_handle(vpiStmt, tf);
    ASSERT_NE(control, nullptr) << var_name;
    vpiHandle block = vpi_handle(vpiCondition, control);
    ASSERT_NE(block, nullptr) << var_name;
    EXPECT_EQ(vpi_get(vpiType, block), vpiClockingBlock) << var_name;
    vpiHandle var = vpi_handle(vpiPrefix, block);
    ASSERT_NE(var, nullptr) << var_name;
    EXPECT_EQ(vpi_get(vpiType, var), vpiVirtualInterfaceVar) << var_name;
    EXPECT_STREQ(vpi_get_str(vpiName, var), var_name);
    EXPECT_EQ(vpi_handle(vpiActual, block), nullptr) << var_name;
  }

  static void ExpectBlockPrefixedBy(const char* task, const char* var_name) {
    ExpectBlockPrefixedBy(Named(vpiTaskFunc, By("top"), task), var_name);
  }
};

TEST_F(ClockingBlocksOfARun,
       AVirtualInterfacesClockingBlockHasPrefixAndActual) {
  Run("interface bus(input logic clk);\n"
      "  clocking first @(negedge clk); endclocking\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; bus b(clk); virtual bus vif, vu;\n"
      "  initial vif = b;\n"
      "  task wait_bound; @(vif.cb); endtask\n"
      "  task wait_unbound; @(vu.cb); endtask\n"
      "  task wait_signal; @(vif.clk); endtask\n"
      "endmodule\n");
  ASSERT_NE(Named(vpiTaskFunc, By("top"), "wait_bound"), nullptr);
  vpiHandle control = ControlOf("wait_bound");
  ASSERT_NE(control, nullptr);
  ASSERT_EQ(vpi_get(vpiType, control), vpiEventControl);
  vpiHandle bound = vpi_handle(vpiCondition, control);
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bound), vpiClockingBlock);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, bound)),
            VpiObjectOf(By("top.vif")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, bound)),
            VpiObjectOf(Named(vpiClockingBlock, By("top.b"), "cb")));
  vpiHandle unbound = vpi_handle(vpiCondition, ControlOf("wait_unbound"));
  ASSERT_NE(unbound, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, unbound)),
            VpiObjectOf(By("top.vu")));
  EXPECT_EQ(vpi_handle(vpiActual, unbound), nullptr);
  vpiHandle signal = vpi_handle(vpiCondition, ControlOf("wait_signal"));
  ASSERT_NE(signal, nullptr);
  EXPECT_EQ(vpi_get(vpiType, signal), vpiRefObj);
}

TEST_F(ClockingBlocksOfARun,
       ATasksVirtualInterfacesClockingBlockHasPrefixAndActual) {
  Run("interface bus(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; bus b(clk);\n"
      "  task wait_arg(virtual bus v); @(v.cb); endtask\n"
      "  task wait_local; virtual bus lv; @(lv.cb); endtask\n"
      "endmodule\n");
  ExpectBlockPrefixedBy("wait_arg", "v");
  ExpectBlockPrefixedBy("wait_local", "lv");
}

TEST_F(ClockingBlocksOfARun,
       ATypedefVirtualInterfacesClockingBlockHasPrefixAndActual) {
  Run("interface bus(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; bus b(clk);\n"
      "  typedef virtual bus vbus_t; vbus_t mv;\n"
      "  task wait_module; @(mv.cb); endtask\n"
      "  task wait_arg(vbus_t v); @(v.cb); endtask\n"
      "endmodule\n");
  ExpectBlockPrefixedBy("wait_module", "mv");
  ExpectBlockPrefixedBy("wait_arg", "v");
}

TEST_F(ClockingBlocksOfARun,
       AnUninstantiatedInterfacesClockingBlockHasPrefixAndActual) {
  Run("interface bus(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; virtual bus vif;\n"
      "  task wait_block; @(vif.cb); endtask\n"
      "  task wait_signal; @(vif.clk); endtask\n"
      "endmodule\n");
  ExpectBlockPrefixedBy("wait_block", "vif");
  vpiHandle control = ControlOf("wait_signal");
  ASSERT_NE(control, nullptr);
  vpiHandle signal = vpi_handle(vpiCondition, control);
  ASSERT_NE(signal, nullptr);
  EXPECT_EQ(vpi_get(vpiType, signal), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, signal)),
            VpiObjectOf(By("top.vif")));
}

TEST_F(ClockingBlocksOfARun,
       AClassPropertysVirtualInterfaceClockingBlockHasPrefixAndActual) {
  Run("interface bus(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; bus b(clk);\n"
      "  class C; virtual bus vif; task run; @(vif.cb); endtask endclass\n"
      "endmodule\n");
  ExpectBlockPrefixedBy(
      Named(vpiTaskFunc, Named(vpiClassDefn, By("top"), "C"), "run"), "vif");
}

TEST_F(ClockingBlocksOfARun,
       APackagesVirtualInterfaceClockingBlockHasPrefixAndActual) {
  Run("interface bus(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "package pkg; virtual bus vif; task run; @(vif.cb); endtask\n"
      "endpackage\n"
      "module top; logic clk; bus b(clk); endmodule\n");
  ExpectBlockPrefixedBy(Named(vpiTaskFunc, By("pkg"), "run"), "vif");
}

TEST_F(ClockingBlocksOfARun, ADefaultClockingBlockIsReachedFromItsModule) {
  Run("module top; logic clk, a, b;\n"
      "  default clocking cb @(posedge clk); input a; output b; endclocking\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle cb = Named(vpiClockingBlock, top, "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, cb), "top.cb");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDefaultClocking, top)), VpiObjectOf(cb));
  vpiHandle event = vpi_handle(vpiClockingEvent, cb);
  ASSERT_NE(event, nullptr);
  EXPECT_EQ(vpi_get(vpiType, event), vpiEventControl);
}

TEST_F(ClockingBlocksOfARun, AClockingBlockReachesItsIoDecls) {
  Run("module top; logic clk, a, b;\n"
      "  clocking cb @(posedge clk); input a; output b; endclocking\n"
      "endmodule\n");
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(vpi_handle(vpiDefaultClocking, By("top")), nullptr);
  vpiHandle it = vpi_iterate(vpiClockingIODecl, cb);
  ASSERT_NE(it, nullptr);
  vpiHandle a = vpi_scan(it);
  vpiHandle b = vpi_scan(it);
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, a), "a");
  EXPECT_EQ(vpi_get(vpiDirection, a), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, b), vpiOutput);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, b)), VpiObjectOf(By("top.b")));
}

TEST_F(ClockingBlocksOfARun, SkewsAndEdgesAreTheBlocksDefaultsAndAnIoDeclsOwn) {
  Run("module top; logic clk, a, b, c;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input negedge #2 output #3;\n"
      "    input posedge #1 a; input c; output b;\n"
      "  endclocking\n"
      "endmodule\n");
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(vpi_get(vpiInputEdge, cb), vpiNegedge);
  EXPECT_EQ(vpi_get(vpiOutputEdge, cb), vpiNoEdge);
  vpiHandle in_skew = vpi_handle(vpiInputSkew, cb);
  ASSERT_NE(in_skew, nullptr);
  EXPECT_EQ(vpi_get(vpiType, in_skew), vpiDelayControl);
  vpiHandle a = Named(vpiClockingIODecl, cb, "a");
  vpiHandle b = Named(vpiClockingIODecl, cb, "b");
  vpiHandle c = Named(vpiClockingIODecl, cb, "c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiInputEdge, a), vpiPosedge);
  EXPECT_EQ(vpi_get(vpiInputEdge, c), vpiNegedge);
  EXPECT_EQ(vpi_handle(vpiInputSkew, b), nullptr);
  vpiHandle out_skew = vpi_handle(vpiOutputSkew, b);
  ASSERT_NE(out_skew, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(out_skew, &value);
  EXPECT_EQ(value.value.integer, 3);
}

TEST_F(ClockingBlocksOfARun, AGenerateBlocksClockingBlockIsItsGenScopes) {
  Run("module top; logic clk, a;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    clocking cb @(posedge clk); input a; endclocking\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(vpi_iterate(vpiClockingBlock, By("top")), nullptr);
  vpiHandle g1 = By("top.g[1]");
  ASSERT_NE(g1, nullptr);
  vpiHandle cb = Named(vpiClockingBlock, g1, "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, cb), "top.g[1].cb");
  vpiHandle a = Named(vpiClockingIODecl, cb, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, a)), VpiObjectOf(By("top.a")));
}

TEST_F(ClockingBlocksOfARun, AClockingBlocksNameIsTheBlockAndNoVariable) {
  Run("module top; logic clk;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  task wait_block; @(cb); endtask\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(Named(vpiVariables, top, "cb"), nullptr);
  vpiHandle cb = By("top.cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(vpi_get(vpiType, cb), vpiClockingBlock);
  vpiHandle control = ControlOf("wait_block");
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, control)), VpiObjectOf(cb));
}

TEST(ClockingBlockModel, ANetHasNoClockingEdges) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiInputEdge, VpiHandleOf(&net)), vpiUndefined);
  EXPECT_EQ(vpi_get(vpiOutputEdge, VpiHandleOf(&net)), vpiUndefined);
  SetGlobalVpiContext(nullptr);
}

TEST_F(ClockingBlocksOfARun,
       ANestedInterfacesVirtualInterfaceClockingBlockHasPrefixAndActual) {
  Run("module top; logic clk;\n"
      "  interface bus(input logic clk);\n"
      "    clocking cb @(posedge clk); endclocking\n"
      "  endinterface\n"
      "  virtual bus vif;\n"
      "  task wait_module; @(vif.cb); endtask\n"
      "  task wait_arg(virtual bus v); @(v.cb); endtask\n"
      "  task wait_local; virtual bus lv; @(lv.cb); endtask\n"
      "  class C; virtual bus cv; task run; @(cv.cb); endtask endclass\n"
      "endmodule\n");
  ExpectBlockPrefixedBy("wait_module", "vif");
  ExpectBlockPrefixedBy("wait_arg", "v");
  ExpectBlockPrefixedBy("wait_local", "lv");
  ExpectBlockPrefixedBy(
      Named(vpiTaskFunc, Named(vpiClassDefn, By("top"), "C"), "run"), "cv");
}

}  // namespace
}  // namespace delta
