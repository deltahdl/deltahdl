#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleByIndexSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiHandleByIndexSim, AModulesIndexNamesNoPort) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  vpi_ctx_.CreatePort("b", kVpiOutput, mod);

  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(mod), 1), nullptr);
}

TEST_F(VpiHandleByIndexSim, HandleByIndexNullParentReturnsNullptr) {
  vpiHandle result = vpi_handle_by_index(nullptr, 0);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiHandleByIndexSim, HandleByIndexOutOfRangeReturnsNullptr) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  vpi_ctx_.CreatePort("bus0", kVpiInput, bus);
  vpiHandle result = vpi_handle_by_index(VpiHandleOf(bus), 99);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiHandleByIndexSim, HandleByIndexProtectedObjectIsAnError) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  mod->is_protected = true;

  vpiHandle result = vpi_handle_by_index(VpiHandleOf(mod), 0);
  EXPECT_EQ(result, nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

TEST_F(VpiHandleByIndexSim,
       HandleByIndexReferenceWithoutAccessByIndexReturnsNullptr) {
  auto* param = vpi_ctx_.CreateParameter("p", 0);
  vpi_ctx_.CreatePort("a", kVpiInput, param);

  vpiHandle result = vpi_handle_by_index(VpiHandleOf(param), 0);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiHandleByIndexSim, HandleByIndexSelectsRegArrayElement) {
  Variable* e0 = sim_ctx_.CreateVariable("m0", 8);
  Variable* e1 = sim_ctx_.CreateVariable("m1", 8);
  Variable* e2 = sim_ctx_.CreateVariable("m2", 8);
  auto* array =
      vpi_ctx_.CreateRegArray("mem", vpiStaticArray, {{0, 1, 2}}, {e0, e1, e2});

  vpiHandle result = vpi_handle_by_index(VpiHandleOf(array), 1);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(VpiObjectOf(result), array->children[1]);
  EXPECT_EQ(vpi_get(vpiType, result), vpiReg);

  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(array), 3), nullptr);
}

TEST_F(VpiHandleByIndexSim, HandleByIndexSelectsNetBit) {
  VpiObject net;
  net.type = kVpiNet;
  VpiObject bit0, bit1, bit2, bit3;
  bit0.type = kVpiNet;
  bit0.index = 0;
  bit1.type = kVpiNet;
  bit1.index = 1;
  bit2.type = kVpiNet;
  bit2.index = 2;
  bit3.type = kVpiNet;
  bit3.index = 3;
  net.children = {&bit0, &bit1, &bit2, &bit3};

  vpiHandle result = vpi_handle_by_index(VpiHandleOf(&net), 2);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(VpiObjectOf(result), &bit2);

  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(&net), 4), nullptr);
}

TEST_F(VpiHandleByIndexSim, AQueueElementNeedsARun) {
  QueueObject queue;
  VpiObject array;
  array.type = vpiRegArray;
  array.queue = &queue;
  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(&array), 0), nullptr);
}

class HandleByIndexOfARun : public VpiDesignRun {
 protected:
  static int ValueAt(vpiHandle ref, PLI_INT32 index) {
    vpiHandle obj = vpi_handle_by_index(ref, index);
    if (obj == nullptr) return -1;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(HandleByIndexOfARun, AScalarNetsLoadPortIsNoIndexedSubobject) {
  Run("module ram(input a, input b); endmodule\n"
      "module top; wire a, trinet; ram r0(a, !trinet); endmodule\n");
  vpiHandle trinet = By("top.trinet");
  ASSERT_NE(trinet, nullptr);
  ASSERT_NE(vpi_iterate(vpiLoad, trinet), nullptr);
  EXPECT_EQ(vpi_handle_by_index(trinet, 1), nullptr);
}

TEST_F(HandleByIndexOfARun, AScalarNetsDriversAreNoIndexedSubobjects) {
  Run("module top; wire a, b, w, f; and g(w, a, b);\n"
      "  initial force f = 1'b1; endmodule\n");
  for (const char* name : {"top.w", "top.f"}) {
    vpiHandle net = By(name);
    ASSERT_NE(net, nullptr) << name;
    EXPECT_EQ(ObjectsOf(vpiDriver, net).size(), 1U) << name;
    EXPECT_EQ(vpi_handle_by_index(net, 0), nullptr) << name;
  }
}

TEST_F(HandleByIndexOfARun, AnArraysVarSelectIsNoIndexedSubobject) {
  Run("module top; int a[1:2]; int i; initial a[i] = 1; endmodule\n");
  vpiHandle a = By("top.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(ObjectsOf(vpiVarSelect, a).size(), 1U);
  EXPECT_EQ(vpi_handle_by_index(a, 0), nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(a, 1)), vpiIntVar);
}

TEST_F(HandleByIndexOfARun,
       AnInstanceThatIsNoArrayElementHasNoIndexedSubobject) {
  Run("module ram(input a, input b); endmodule\n"
      "module top; wire a, trinet; ram r0(a, !trinet); endmodule\n");
  vpiHandle r0 = By("top.r0");
  ASSERT_NE(r0, nullptr);
  ASSERT_NE(vpi_iterate(vpiPort, r0), nullptr);
  EXPECT_EQ(vpi_handle_by_index(r0, 0), nullptr);
  EXPECT_EQ(vpi_handle_by_index(r0, 1), nullptr);
  PLI_INT32 second[] = {1};
  EXPECT_EQ(vpi_handle_by_multi_index(r0, 1, second), nullptr);
}

TEST_F(HandleByIndexOfARun, APackedStructVarIndexesItsBits) {
  Run("module top; struct packed { logic [1:0] a; logic b; } ps;\n"
      "  struct { logic a; } us; initial $noop; endmodule\n");
  vpiHandle ps = By("top.ps");
  ASSERT_NE(ps, nullptr);
  vpiHandle bit = vpi_handle_by_index(ps, 2);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bit), vpiVarBit);
  EXPECT_EQ(vpi_compare_objects(bit, vpi_handle_by_index(By("top.ps.a"), 1)),
            1);
  EXPECT_EQ(vpi_handle_by_index(ps, 3), nullptr);
  vpiHandle us = By("top.us");
  ASSERT_NE(us, nullptr);
  EXPECT_EQ(vpi_handle_by_index(us, 0), nullptr);
}

TEST_F(HandleByIndexOfARun, ANetIsIndexedThroughItsDeclaredRange) {
  Run("module top; wire [7:4] n = 4'b0001; wire [0:3] m = 4'b0001;\n"
      "  initial $noop; endmodule\n");
  vpiHandle n = By("top.n");
  vpiHandle m = By("top.m");
  ASSERT_NE(n, nullptr);
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(n, 4)), vpiNetBit);
  EXPECT_EQ(ValueAt(n, 4), 1);
  EXPECT_EQ(ValueAt(n, 7), 0);
  EXPECT_EQ(vpi_handle_by_index(n, 0), nullptr);
  EXPECT_EQ(ValueAt(m, 3), 1);
  EXPECT_EQ(ValueAt(m, 0), 0);
  EXPECT_EQ(vpi_handle_by_index(m, 4), nullptr);
}

TEST_F(HandleByIndexOfARun,
       DISABLED_APackedMultidimensionalVectorYieldsItsSubvector) {
  Run("module top; logic [1:0][3:0] v = 8'hA6;\n"
      "  wire [1:0][2:0] w = 6'b101_011; initial $noop; endmodule\n");
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  vpiHandle upper = vpi_handle_by_index(v, 1);
  ASSERT_NE(upper, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, upper), 4);
  EXPECT_EQ(ValueAt(v, 1), 0xA);
  EXPECT_EQ(ValueAt(v, 0), 0x6);
  EXPECT_EQ(ValueAt(upper, 3), 1);
  EXPECT_EQ(ValueAt(upper, 0), 0);
  vpiHandle w = By("top.w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, vpi_handle_by_index(w, 1)), 3);
  EXPECT_EQ(ValueAt(w, 1), 5);
  EXPECT_EQ(ValueAt(w, 0), 3);
}

TEST_F(HandleByIndexOfARun, AVariableRangeBelowZeroIsIndexedByItsBounds) {
  Run("module top; logic [-1:-4] v = 4'b0001; initial $noop; endmodule\n");
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(v, -4)), vpiVarBit);
  EXPECT_EQ(ValueAt(v, -4), 1);
  EXPECT_EQ(ValueAt(v, -1), 0);
  EXPECT_EQ(vpi_handle_by_index(v, 0), nullptr);
}

TEST_F(HandleByIndexOfARun, DISABLED_ANetArrayBelowZeroIsIndexedByItsBounds) {
  Run("module top; wire n [-1:0]; assign n[-1] = 1'b1; assign n[0] = 1'b0;\n"
      "  initial $noop; endmodule\n");
  vpiHandle n = By("top.n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(ValueAt(n, -1), 1);
  EXPECT_EQ(ValueAt(n, 0), 0);
  EXPECT_EQ(vpi_handle_by_index(n, 1), nullptr);
}

TEST_F(HandleByIndexOfARun, AVectorPortIsIndexedIntoItsPortBits) {
  Run("module sub(input logic [5:2] a); endmodule\n"
      "module top; logic [5:2] x; sub u(x); endmodule\n");
  vpiHandle port = Named(vpiPort, By("top.u"), "a");
  ASSERT_NE(port, nullptr);
  vpiHandle bit = vpi_handle_by_index(port, 3);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bit), vpiPortBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, bit)), VpiObjectOf(port));
  EXPECT_EQ(vpi_handle_by_index(port, 1), nullptr);
}

TEST_F(HandleByIndexOfARun, ADynamicArrayIsIndexedUpToItsSize) {
  Run("module top; int d[];\n"
      "  initial begin d = new[3]; d = '{7, 8, 9}; $noop; end endmodule\n");
  vpiHandle d = By("top.d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(ValueAt(d, 0), 7);
  EXPECT_EQ(ValueAt(d, 2), 9);
  EXPECT_EQ(vpi_handle_by_index(d, 3), nullptr);
  EXPECT_EQ(vpi_handle_by_index(d, -1), nullptr);
}

TEST_F(HandleByIndexOfARun, AnAssociativeArrayIsIndexedOnlyByItsKeys) {
  Run("module top; int aa[int];\n"
      "  initial begin aa[5] = 50; aa[-2] = 20; $noop; end endmodule\n");
  vpiHandle aa = By("top.aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_EQ(ValueAt(aa, 5), 50);
  EXPECT_EQ(ValueAt(aa, -2), 20);
  EXPECT_EQ(vpi_handle_by_index(aa, 4), nullptr);
  EXPECT_EQ(vpi_handle_by_index(aa, 0), nullptr);
}

}  // namespace
}  // namespace delta
