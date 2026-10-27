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

// §38.19 with §37.10: a module has no access by index, its ports being reached
// by iteration, so an index matching a port's place names nothing (#7404).
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

// §38.19: an index that names no sub-object does not lead to a legal index
// select expression, so the routine returns a null handle.
TEST_F(VpiHandleByIndexSim, HandleByIndexOutOfRangeReturnsNullptr) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", /*net_ptr=*/nullptr, /*width=*/8);
  vpi_ctx_.CreatePort("bus0", kVpiInput, bus);
  vpiHandle result = vpi_handle_by_index(VpiHandleOf(bus), 99);
  EXPECT_EQ(result, nullptr);
}

// §38.19: unless otherwise specified, calling vpi_handle_by_index() for a
// protected reference object is an error - no handle is produced and the error
// status is recorded for vpi_chk_error() (§38.2).
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

// §38.19: the reference object must have the access-by-index property. A
// parameter offers no index-selected relationship, so even when it has a child
// at the requested index the routine builds no index select and returns null.
TEST_F(VpiHandleByIndexSim,
       HandleByIndexReferenceWithoutAccessByIndexReturnsNullptr) {
  auto* param = vpi_ctx_.CreateParameter("p", 0);
  vpi_ctx_.CreatePort("a", kVpiInput, param);  // gives param a child at index 0

  vpiHandle result = vpi_handle_by_index(VpiHandleOf(param), 0);
  EXPECT_EQ(result, nullptr);
}

// §38.19: the LRM names a reg array as a reference object whose index selects
// an array element (obj is the array). A reg array carries the access-by-index
// property, so selecting an in-range element index returns the handle to that
// element - a distinct reference-object input form from the module/port case.
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

  // An element index past the last array element names no sub-object, so the
  // selection is not a legal index select expression and the handle is null.
  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(array), 3), nullptr);
}

// §38.19: the LRM's first example names a net as a reference object whose index
// selects one of the net's bits (obj is the net). A net carries the
// access-by-index property, so selecting an in-range bit index returns the
// handle to that bit - the net/bit reference-object input form, distinct from
// the module/port and reg-array/element forms already covered.
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

  // A bit index beyond the net width names no sub-object, so no legal index
  // select is formed and the handle is null.
  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(&net), 4), nullptr);
}

// §38.19 with §37.17: an element of a queue lives in the run's store of the
// queue and is made when first selected, so with no run there is none.
TEST_F(VpiHandleByIndexSim, AQueueElementNeedsARun) {
  QueueObject queue;
  VpiObject array;
  array.type = vpiRegArray;
  array.queue = &queue;
  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(&array), 0), nullptr);
}

class HandleByIndexOfARun : public VpiDesignRun {};

// §38.19 with §37.46: a port connected to an expression reading a scalar net
// hangs among the net's children as one of its loads, but is no sub-object an
// index into the net selects, so the index names nothing there (#7360).
TEST_F(HandleByIndexOfARun, AScalarNetsLoadPortIsNoIndexedSubobject) {
  Run("module ram(input a, input b); endmodule\n"
      "module top; wire a, trinet; ram r0(a, !trinet); endmodule\n");
  vpiHandle trinet = By("top.trinet");
  ASSERT_NE(trinet, nullptr);
  ASSERT_NE(vpi_iterate(vpiLoad, trinet), nullptr);
  EXPECT_EQ(vpi_handle_by_index(trinet, 1), nullptr);
}

// §38.19 with §37.46: the terminal of a gate driving a scalar net, and the
// force of the net, hang among the net's children as its drivers, each with
// the index of its place, 0 for the gate's output and the force alike, but
// neither is a sub-object an index into the net selects, so 0 names nothing.
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

// §38.19 with §37.19: a var select of an array var hangs among the array's
// children, but which element it stands for varies as its index does, so it
// is no sub-object an index selects: into an array of elements 1 and 2, 0
// names nothing, and 1 the element.
TEST_F(HandleByIndexOfARun, AnArraysVarSelectIsNoIndexedSubobject) {
  Run("module top; int a[1:2]; int i; initial a[i] = 1; endmodule\n");
  vpiHandle a = By("top.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(ObjectsOf(vpiVarSelect, a).size(), 1U);
  EXPECT_EQ(vpi_handle_by_index(a, 0), nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(a, 1)), vpiIntVar);
}

// §38.19 with §37.10: a module instance that is no element of an instance
// array has no access by index, so no index into it is a legal index select
// and each names nothing, though the instance holds ports and nets (#7404).
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

// §38.19 with §37.17 details 12 and 20: a packed struct var indexes its var
// bits, so an index into it selects the bit of that index, and an index
// beyond its bits, or into an unpacked struct, whose members carry no index,
// selects nothing.
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

}  // namespace
}  // namespace delta
