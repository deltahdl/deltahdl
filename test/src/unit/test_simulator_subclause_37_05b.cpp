#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ModuleContentsOfARun : public VpiDesignRun {
 protected:
  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  void RunAllTops(const std::string& src) {
    RtlirDesign* design = ElaborateSrcAllTops(src, f_);
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.has_errors);
    LowerAndRun(design, f_);
  }
};

TEST_F(ModuleContentsOfARun, InternalScopesAreTheSubroutinesBlocksAndClocking) {
  Run("module top; logic clk;\n"
      "  task t; endtask\n"
      "  function int f; return 0; endfunction\n"
      "  if (1) begin : g end\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiInternalScope, By("top")),
            (std::vector<std::string>{"cb", "f", "g", "t"}));
}

TEST_F(ModuleContentsOfARun, AModuleReachesOneObjectPerInterfaceArray) {
  Run("interface ifc; endinterface\n"
      "module top; ifc ifs[0:1] (); ifc one (); endmodule\n");
  std::vector<vpiHandle> arrays = ObjectsOf(vpiInterfaceArray, By("top"));
  ASSERT_EQ(arrays.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, arrays[0]), vpiInterfaceArray);
  EXPECT_EQ(NameOf(arrays[0]), "ifs");
}

TEST_F(ModuleContentsOfARun,
       DISABLED_ADefaultNamedApartReachesTheDeclaredBlock) {
  Run("module top; logic clk;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  std::vector<vpiHandle> blocks = ObjectsOf(vpiClockingBlock, By("top"));
  ASSERT_EQ(blocks.size(), 1U);
  vpiHandle dflt = vpi_handle(vpiDefaultClocking, By("top"));
  ASSERT_NE(dflt, nullptr);
  EXPECT_EQ(VpiObjectOf(dflt), VpiObjectOf(blocks[0]));
}

TEST_F(ModuleContentsOfARun, AnUnnamedDefaultClockingBlockIsReached) {
  Run("module top; logic clk;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "endmodule\n");
  vpiHandle dflt = vpi_handle(vpiDefaultClocking, By("top"));
  ASSERT_NE(dflt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, dflt), vpiClockingBlock);
}

TEST_F(ModuleContentsOfARun, AModulesGlobalClockingIsReached) {
  Run("module top; logic clk;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "endmodule\n");
  EXPECT_EQ(NameOf(vpi_handle(vpiGlobalClocking, By("top"))), "gclk");
}

TEST_F(ModuleContentsOfARun, AModuleWithNoGlobalClockingReachesNone) {
  Run("module top; logic clk;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "endmodule\n");
  EXPECT_EQ(vpi_handle(vpiGlobalClocking, By("top")), nullptr);
}

TEST_F(ModuleContentsOfARun, AnInterfacesDefaultClockingIsReached) {
  Run("interface ifc(input logic clk);\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; ifc i (clk); endmodule\n");
  EXPECT_EQ(NameOf(vpi_handle(vpiDefaultClocking, By("top.i"))), "cb");
}

TEST_F(ModuleContentsOfARun, AnInterfacesGlobalClockingIsReached) {
  Run("interface ifc(input logic clk);\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; ifc i (clk); endmodule\n");
  EXPECT_EQ(NameOf(vpi_handle(vpiGlobalClocking, By("top.i"))), "gclk");
}

TEST_F(ModuleContentsOfARun, AnInterfaceReachesEachOfItsTwoClockingBlocks) {
  Run("interface ifc(input logic clk);\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  global clocking gclk @(negedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; ifc i (clk); endmodule\n");
  vpiHandle dflt = vpi_handle(vpiDefaultClocking, By("top.i"));
  vpiHandle global = vpi_handle(vpiGlobalClocking, By("top.i"));
  EXPECT_EQ(NameOf(dflt), "cb");
  EXPECT_EQ(NameOf(global), "gclk");
  EXPECT_NE(VpiObjectOf(dflt), VpiObjectOf(global));
}

TEST_F(ModuleContentsOfARun, AnInterfacesPlainClockingBlockIsNotItsDefault) {
  Run("interface ifc(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; ifc i (clk); endmodule\n");
  ASSERT_EQ(ObjectsOf(vpiClockingBlock, By("top.i")).size(), 1U);
  EXPECT_EQ(vpi_handle(vpiDefaultClocking, By("top.i")), nullptr);
}

TEST_F(ModuleContentsOfARun, AnInterfaceWithNoClockingReachesNeither) {
  Run("interface ifc; endinterface\n"
      "module top; ifc i (); endmodule\n");
  EXPECT_EQ(vpi_handle(vpiDefaultClocking, By("top.i")), nullptr);
  EXPECT_EQ(vpi_handle(vpiGlobalClocking, By("top.i")), nullptr);
}

TEST_F(ModuleContentsOfARun, AProgramsDefaultClockingIsReached) {
  Run("program prg(input logic clk);\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "endprogram\n"
      "module top; logic clk; prg p (clk); endmodule\n");
  EXPECT_EQ(NameOf(vpi_handle(vpiDefaultClocking, By("top.p"))), "cb");
}

TEST_F(ModuleContentsOfARun,
       DISABLED_AProgramsDefaultNamedApartReachesTheBlock) {
  Run("program prg(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  default clocking cb;\n"
      "endprogram\n"
      "module top; logic clk; prg p (clk); endmodule\n");
  std::vector<vpiHandle> blocks = ObjectsOf(vpiClockingBlock, By("top.p"));
  ASSERT_EQ(blocks.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDefaultClocking, By("top.p"))),
            VpiObjectOf(blocks[0]));
}

TEST_F(ModuleContentsOfARun, AProgramWithNoDefaultClockingReachesNone) {
  Run("program prg(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endprogram\n"
      "module top; logic clk; prg p (clk); endmodule\n");
  EXPECT_EQ(vpi_handle(vpiDefaultClocking, By("top.p")), nullptr);
}

TEST_F(ModuleContentsOfARun, AModuleOutsideAnArrayHasNoIndex) {
  Run("module sub; endmodule\n"
      "module top; sub one (); sub arr[1:0] (); endmodule\n");
  ASSERT_NE(By("top.one"), nullptr);
  EXPECT_EQ(vpi_handle(vpiIndex, By("top.one")), nullptr);
  ASSERT_NE(By("top"), nullptr);
  EXPECT_EQ(vpi_handle(vpiIndex, By("top")), nullptr);
}

TEST_F(ModuleContentsOfARun, AnInterfaceElementReachesItsIndex) {
  Run("interface ifc; endinterface\n"
      "module top; ifc ifs[2:4] (); endmodule\n");
  vpiHandle element = By("top.ifs[3]");
  ASSERT_NE(element, nullptr);
  vpiHandle index = vpi_handle(vpiIndex, element);
  ASSERT_NE(index, nullptr);
  EXPECT_EQ(IntOf(index), 3);
}

TEST_F(ModuleContentsOfARun, AnInterfaceOutsideAnArrayHasNoIndex) {
  Run("interface ifc; endinterface\n"
      "module top; ifc one (); ifc ifs[1:0] (); endmodule\n");
  ASSERT_NE(By("top.one"), nullptr);
  EXPECT_EQ(vpi_handle(vpiIndex, By("top.one")), nullptr);
}

TEST_F(ModuleContentsOfARun, AProgramElementReachesItsIndex) {
  Run("program prg; endprogram\n"
      "module top; prg p[1:2] (); endmodule\n");
  vpiHandle element = By("top.p[2]");
  ASSERT_NE(element, nullptr);
  vpiHandle index = vpi_handle(vpiIndex, element);
  ASSERT_NE(index, nullptr);
  EXPECT_EQ(IntOf(index), 2);
}

TEST_F(ModuleContentsOfARun, AProgramOutsideAnArrayHasNoIndex) {
  Run("program prg; endprogram\n"
      "module top; prg one (); prg p[1:0] (); endmodule\n");
  ASSERT_NE(By("top.one"), nullptr);
  EXPECT_EQ(vpi_handle(vpiIndex, By("top.one")), nullptr);
}

TEST_F(ModuleContentsOfARun, EveryUninstantiatedModuleIsATopModule) {
  RunAllTops(
      "module a; endmodule\n"
      "module b; endmodule\n");
  EXPECT_EQ(NamesOf(vpiModule, nullptr), (std::vector<std::string>{"a", "b"}));
}

TEST_F(ModuleContentsOfARun, TopLevelInterfacesAndProgramsAreNotModules) {
  RunAllTops(
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "module top; endmodule\n");
  EXPECT_EQ(NamesOf(vpiModule, nullptr), (std::vector<std::string>{"top"}));
}

}  // namespace
}  // namespace delta
