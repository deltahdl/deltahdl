#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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

TEST_F(VpiHandleByIndexSim, HandleByIndexReturnCorrectChild) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);

  vpiHandle result = vpi_handle_by_index(mod, 1);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, port_b);
}

TEST_F(VpiHandleByIndexSim, HandleByIndexNullParentReturnsNullptr) {
  vpiHandle result = vpi_handle_by_index(nullptr, 0);
  EXPECT_EQ(result, nullptr);
}

// §38.19: an index that names no sub-object does not lead to a legal index
// select expression, so the routine returns a null handle.
TEST_F(VpiHandleByIndexSim, HandleByIndexOutOfRangeReturnsNullptr) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpiHandle result = vpi_handle_by_index(mod, 99);
  EXPECT_EQ(result, nullptr);
}

// §38.19: unless otherwise specified, calling vpi_handle_by_index() for a
// protected reference object is an error - no handle is produced and the error
// status is recorded for vpi_chk_error() (§38.2).
TEST_F(VpiHandleByIndexSim, HandleByIndexProtectedObjectIsAnError) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  mod->is_protected = true;

  vpiHandle result = vpi_handle_by_index(mod, 0);
  EXPECT_EQ(result, nullptr);

  SVpiErrorInfo info = {};
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

  vpiHandle result = vpi_handle_by_index(param, 0);
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

  vpiHandle result = vpi_handle_by_index(array, 1);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, array->children[1]);
  EXPECT_EQ(vpi_get(vpiType, result), vpiReg);

  // An element index past the last array element names no sub-object, so the
  // selection is not a legal index select expression and the handle is null.
  EXPECT_EQ(vpi_handle_by_index(array, 3), nullptr);
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

  vpiHandle result = vpi_handle_by_index(&net, 2);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, &bit2);

  // A bit index beyond the net width names no sub-object, so no legal index
  // select is formed and the handle is null.
  EXPECT_EQ(vpi_handle_by_index(&net, 4), nullptr);
}

}  // namespace
}  // namespace delta
