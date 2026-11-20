#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Interface : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(Interface, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiInterface;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, VpiHandleOf(&member))),
            &index_expr);
}

TEST_F(Interface, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiInterface;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&standalone)), nullptr);
}

TEST_F(Interface, IndexTransitionIsNullForArrayElementWithoutIndexExpr) {
  VpiObject child_expr;
  child_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiInterface;
  member.array_member = true;
  member.index_expr = nullptr;
  member.children.push_back(&child_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&member)), nullptr);
}

TEST_F(Interface, AnInterfaceIteratesItsModPathsAndEachReachesIt) {
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject path;
  path.type = vpiModPath;
  path.parent = &iface;
  VpiObject other;
  other.type = vpiNet;
  other.parent = &iface;
  iface.children = {&other, &path};

  vpiHandle it = vpi_iterate(vpiModPath, VpiHandleOf(&iface));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &path);
  EXPECT_EQ(vpi_scan(it), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&path))), &iface);
}

class InterfacesOfARun : public VpiDesignRun {};

constexpr const char* kInterfaceInstance =
    "interface ifc; logic d; endinterface\n"
    "module top; ifc i0(); endmodule\n";

TEST_F(InterfacesOfARun, AnInterfaceInstanceIsReachedAsAnInterface) {
  Run(kInterfaceInstance);
  EXPECT_EQ(NamesOf(vpiInterface, vpi_handle_by_name(VpiText("top"), nullptr)),
            (std::vector<std::string>{"i0"}));
}

TEST_F(InterfacesOfARun, AnInterfaceInstanceIsOfTypeInterface) {
  Run(kInterfaceInstance);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_name(VpiText("top.i0"), nullptr)),
            vpiInterface);
}

TEST_F(InterfacesOfARun, AnInterfaceInstancesDefinitionIsItsInterface) {
  Run(kInterfaceInstance);
  EXPECT_STREQ(
      vpi_get_str(vpiDefName, vpi_handle_by_name(VpiText("top.i0"), nullptr)),
      "ifc");
}

TEST_F(InterfacesOfARun, AnInterfaceIteratesItsContinuousAssignments) {
  Run("interface ifc; wire a, b, c; assign a = b; assign b = c; endinterface\n"
      "module top; ifc i (); endmodule\n");
  EXPECT_EQ(KindsOf(vpiContAssign, By("top.i")),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
}

TEST_F(InterfacesOfARun, AnInterfaceIteratesItsDefaultAndOtherClocking) {
  Run("interface ifc(input logic clk);\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  clocking other @(negedge clk); endclocking\n"
      "endinterface\n"
      "module top; logic clk; ifc i (clk); endmodule\n");
  EXPECT_EQ(NamesOf(vpiClockingBlock, By("top.i")),
            (std::vector<std::string>{"cb", "other"}));
}

TEST_F(InterfacesOfARun, AnInterfaceIteratesAnInterfaceNestedInIt) {
  Run("interface inner; endinterface\n"
      "interface outer; inner n (); endinterface\n"
      "module top; outer o (); endmodule\n");
  EXPECT_EQ(NamesOf(vpiInterface, By("top.o")),
            (std::vector<std::string>{"n"}));
  EXPECT_EQ(vpi_get(vpiType, By("top.o.n")), vpiInterface);
}

TEST_F(InterfacesOfARun, AnInterfaceIteratesAnInterfaceArrayNestedInIt) {
  Run("interface inner; endinterface\n"
      "interface outer; inner arr[0:1] (); inner one (); endinterface\n"
      "module top; outer o (); endmodule\n");
  std::vector<vpiHandle> arrays = ObjectsOf(vpiInterfaceArray, By("top.o"));
  ASSERT_EQ(arrays.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, arrays[0]), vpiInterfaceArray);
  EXPECT_STREQ(vpi_get_str(vpiName, arrays[0]), "arr");
}

TEST_F(InterfacesOfARun, AnInterfaceIteratesItsProcesses) {
  Run("interface ifc; logic d;\n"
      "  initial d = 0;\n"
      "  always @(d) d <= d;\n"
      "  final d = 1;\n"
      "endinterface\n"
      "module top; ifc i (); endmodule\n");
  std::vector<int> kinds = KindsOf(vpiProcess, By("top.i"));
  std::sort(kinds.begin(), kinds.end());
  std::vector<int> expected = {vpiInitial, vpiAlways, vpiFinal};
  std::sort(expected.begin(), expected.end());
  EXPECT_EQ(kinds, expected);
}

constexpr const char* kInterfaceOfEveryKind =
    "interface inner; endinterface\n"
    "interface bus(input logic clk); wire a, b; logic d;\n"
    "  extern task Load();\n"
    "  modport tgt(export Load);\n"
    "  assign a = b;\n"
    "  clocking cb @(posedge clk); endclocking\n"
    "  inner n ();\n"
    "  inner arr[0:1] ();\n"
    "  initial d = 0;\n"
    "endinterface\n"
    "module mem(bus.tgt p); task p.Load(); endtask endmodule\n"
    "module top; logic clk; bus i (clk); mem m (i.tgt); endmodule\n";

TEST_F(InterfacesOfARun, EveryChildKindReachesItsInterfaceAsItsInstance) {
  Run(kInterfaceOfEveryKind);
  vpiHandle iface = By("top.i");
  ASSERT_NE(iface, nullptr);
  for (int kind :
       {vpiInterfaceTfDecl, vpiModport, vpiContAssign, vpiClockingBlock,
        vpiInterface, vpiInterfaceArray, vpiProcess}) {
    std::vector<vpiHandle> children = ObjectsOf(kind, iface);
    EXPECT_FALSE(children.empty()) << kind;
    for (vpiHandle child : children) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, child)), VpiObjectOf(iface))
          << kind;
    }
  }
}

TEST_F(InterfacesOfARun, AnInterfaceHoldingNoneOfAKindIteratesNone) {
  Run("interface ifc; endinterface\n"
      "module top; ifc i (); endmodule\n");
  for (int kind :
       {vpiInterfaceTfDecl, vpiModport, vpiModPath, vpiContAssign,
        vpiClockingBlock, vpiInterface, vpiInterfaceArray, vpiProcess}) {
    EXPECT_EQ(vpi_iterate(kind, By("top.i")), nullptr) << kind;
  }
}

TEST_F(InterfacesOfARun, AnArrayElementIteratesItsInterfacesModports) {
  Run("interface ifc; logic d; modport a(input d); modport b(output d);\n"
      "endinterface\n"
      "module top; ifc ifs[0:1] (); endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.ifs[1]")), vpiInterface);
  EXPECT_EQ(NamesOf(vpiModport, By("top.ifs[1]")),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(InterfacesOfARun, ANestedInterfaceIteratesItsOwnModports) {
  Run("interface inner; logic d; modport in_mp(input d); endinterface\n"
      "interface outer; logic e; modport out_mp(input e); inner n ();\n"
      "endinterface\n"
      "module top; outer o (); endmodule\n");
  EXPECT_EQ(NamesOf(vpiModport, By("top.o.n")),
            (std::vector<std::string>{"in_mp"}));
  EXPECT_EQ(NamesOf(vpiModport, By("top.o")),
            (std::vector<std::string>{"out_mp"}));
}

TEST_F(InterfacesOfARun, AnInterfaceInAGenerateBlockIteratesItsModports) {
  Run("interface ifc; logic d; modport mp(input d); endinterface\n"
      "module top; if (1) begin : g ifc i (); end endmodule\n");
  EXPECT_EQ(NamesOf(vpiModport, By("top.g.i")),
            (std::vector<std::string>{"mp"}));
}

}  // namespace
}  // namespace delta
