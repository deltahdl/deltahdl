#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Program : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(Program, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiProgram;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, VpiHandleOf(&member))),
            &index_expr);
}

TEST_F(Program, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiProgram;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&standalone)), nullptr);
}

TEST_F(Program, TheProcessClassGroupsTheThreeProcedureKinds) {
  EXPECT_TRUE(VpiIsProcessType(vpiInitial));
  EXPECT_TRUE(VpiIsProcessType(vpiFinal));
  EXPECT_TRUE(VpiIsProcessType(vpiAlways));

  EXPECT_FALSE(VpiIsProcessType(vpiProcess));
  EXPECT_FALSE(VpiIsProcessType(vpiContAssign));
}

TEST_F(Program, AProgramIteratesTheProceduresItDeclares) {
  VpiObject initial;
  initial.type = vpiInitial;
  VpiObject assign;
  assign.type = vpiContAssign;
  VpiObject always;
  always.type = vpiAlways;
  VpiObject final_proc;
  final_proc.type = vpiFinal;

  VpiObject program;
  program.type = vpiProgram;
  program.children = {&initial, &assign, &always, &final_proc};

  vpiHandle it = vpi_iterate(vpiProcess, VpiHandleOf(&program));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &initial);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &always);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &final_proc);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(Program, EveryAlwaysFormIsReachedByTheOneEdge) {
  VpiObject comb;
  comb.type = vpiAlways;
  comb.always_type = vpiAlwaysComb;
  VpiObject latch;
  latch.type = vpiAlways;
  latch.always_type = vpiAlwaysLatch;

  VpiObject program;
  program.type = vpiProgram;
  program.children = {&comb, &latch};

  vpiHandle it = vpi_iterate(vpiProcess, VpiHandleOf(&program));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &comb);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &latch);
  EXPECT_EQ(vpi_scan(it), nullptr);

  EXPECT_EQ(vpi_get(vpiAlwaysType, VpiHandleOf(&comb)), vpiAlwaysComb);
  EXPECT_EQ(vpi_get(vpiAlwaysType, VpiHandleOf(&latch)), vpiAlwaysLatch);
}

TEST_F(Program, AProgramOfNoProceduresIteratesToNone) {
  VpiObject assign;
  assign.type = vpiContAssign;

  VpiObject program;
  program.type = vpiProgram;
  program.children = {&assign};

  EXPECT_EQ(vpi_iterate(vpiProcess, VpiHandleOf(&program)), nullptr);
}

TEST_F(Program, AProgramIteratesItsInterfacesAndEachReachesIt) {
  VpiObject program;
  program.type = vpiProgram;
  VpiObject iface;
  iface.type = vpiInterface;
  iface.parent = &program;
  VpiObject array;
  array.type = vpiInterfaceArray;
  array.parent = &program;
  program.children = {&array, &iface};

  vpiHandle ifaces = vpi_iterate(vpiInterface, VpiHandleOf(&program));
  ASSERT_NE(ifaces, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(ifaces)), &iface);
  EXPECT_EQ(vpi_scan(ifaces), nullptr);
  vpiHandle arrays = vpi_iterate(vpiInterfaceArray, VpiHandleOf(&program));
  ASSERT_NE(arrays, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(arrays)), &array);
  EXPECT_EQ(vpi_scan(arrays), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&iface))),
            &program);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&array))),
            &program);
}

class ProgramsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Prog() {
    return vpi_handle_by_name(VpiText("top.p0"), nullptr);
  }
};

constexpr const char* kProgramInstance =
    "program prog; int v; endprogram\n"
    "module top; prog p0(); endmodule\n";

TEST_F(ProgramsOfARun, AProgramInstanceIsReachedAsAProgram) {
  Run(kProgramInstance);
  EXPECT_EQ(NamesOf(vpiProgram, vpi_handle_by_name(VpiText("top"), nullptr)),
            (std::vector<std::string>{"p0"}));
}

TEST_F(ProgramsOfARun, AProgramInstanceIsOfTypeProgram) {
  Run(kProgramInstance);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_name(VpiText("top.p0"), nullptr)),
            vpiProgram);
}

TEST_F(ProgramsOfARun, AProgramInstancesDefinitionIsItsProgram) {
  Run(kProgramInstance);
  EXPECT_STREQ(
      vpi_get_str(vpiDefName, vpi_handle_by_name(VpiText("top.p0"), nullptr)),
      "prog");
}

constexpr const char* kProgramOfEveryKind =
    "program prog(input logic clk); wire a, b, c; int v;\n"
    "  assign a = b;\n"
    "  initial v = 1;\n"
    "  default clocking cb @(posedge clk); endclocking\n"
    "  assign b = c;\n"
    "  final v = 2;\n"
    "  clocking other @(negedge clk); endclocking\n"
    "  initial v = 3;\n"
    "endprogram\n"
    "module top; logic clk; prog p0(clk); endmodule\n";

TEST_F(ProgramsOfARun, AProgramIteratesItsContinuousAssignments) {
  Run(kProgramOfEveryKind);
  EXPECT_EQ(KindsOf(vpiContAssign, Prog()),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
}

TEST_F(ProgramsOfARun, AProgramIteratesItsDefaultAndOtherClocking) {
  Run(kProgramOfEveryKind);
  EXPECT_EQ(NamesOf(vpiClockingBlock, Prog()),
            (std::vector<std::string>{"cb", "other"}));
}

TEST_F(ProgramsOfARun, AProgramIteratesItsProceduresInSourceOrder) {
  Run(kProgramOfEveryKind);
  EXPECT_EQ(KindsOf(vpiProcess, Prog()),
            (std::vector<int>{vpiInitial, vpiFinal, vpiInitial}));
}

TEST_F(ProgramsOfARun, EveryChildOfAProgramReachesItAsItsInstance) {
  Run(kProgramOfEveryKind);
  vpiHandle prog = Prog();
  ASSERT_NE(prog, nullptr);
  for (int kind : {vpiContAssign, vpiClockingBlock, vpiProcess}) {
    std::vector<vpiHandle> children = ObjectsOf(kind, prog);
    EXPECT_FALSE(children.empty()) << kind;
    for (vpiHandle child : children) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, child)), VpiObjectOf(prog))
          << kind;
    }
  }
}

TEST_F(ProgramsOfARun, AProgramHoldingNoneOfAKindIteratesNone) {
  Run("program prog; int v; endprogram\n"
      "module top; prog p0(); endmodule\n");
  for (int kind : {vpiContAssign, vpiClockingBlock, vpiInterface,
                   vpiInterfaceArray, vpiProcess}) {
    EXPECT_EQ(vpi_iterate(kind, Prog()), nullptr) << kind;
  }
}

}  // namespace
}  // namespace delta
