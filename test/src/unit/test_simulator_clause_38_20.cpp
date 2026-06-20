#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiHandleByMultiIndexSim : public ::testing::Test {
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

// §38.20: the routine provides access to the index-selected subobject named by
// the whole list of indices, applied leftmost first and descending one array
// dimension of the reference handle per index. num_index says how many of the
// supplied indices to apply.
TEST_F(VpiHandleByMultiIndexSim, ResolvesNestedSubobjectFromIndexList) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);                  // index 0
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);  // index 1
  vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);             // index 0 within b
  auto* bit_b1 = vpi_ctx_.CreatePort("b1", kVpiOutput, port_b);  // index 1

  int indices[] = {1, 1};
  vpiHandle result = vpi_handle_by_multi_index(mod, 2, indices);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, bit_b1);
}

// §38.20: the indices follow the array dimension declaration from leftmost to
// rightmost, so applying them in the opposite order names a different
// subobject.
TEST_F(VpiHandleByMultiIndexSim, IndicesAreAppliedLeftmostFirst) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port_a = vpi_ctx_.CreatePort("a", kVpiInput, mod);   // index 0
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);  // index 1
  vpi_ctx_.CreatePort("a0", kVpiInput, port_a);              // a[0]
  auto* a1 = vpi_ctx_.CreatePort("a1", kVpiInput, port_a);   // a[1]
  auto* b0 = vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);  // b[0]

  int forward[] = {0, 1};  // a then a[1]
  EXPECT_EQ(vpi_handle_by_multi_index(mod, 2, forward), a1);

  int reversed[] = {1, 0};  // b then b[0]
  EXPECT_EQ(vpi_handle_by_multi_index(mod, 2, reversed), b0);
}

// §38.20: the trailing bit-select index is optional - num_index governs how
// many indices are applied, so a single outer index resolves to the
// intermediate subobject without descending further.
TEST_F(VpiHandleByMultiIndexSim, NumIndexGovernsHowManyIndicesApply) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);                  // index 0
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);  // index 1
  vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);             // index 0 within b

  int indices[] = {1};
  EXPECT_EQ(vpi_handle_by_multi_index(mod, 1, indices), port_b);
}

TEST_F(VpiHandleByMultiIndexSim, NullParentReturnsNullptr) {
  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(nullptr, 1, indices), nullptr);
}

// §38.20: when an index names no subobject the index list does not form a legal
// SystemVerilog index select expression, so the routine returns a null handle.
TEST_F(VpiHandleByMultiIndexSim, IndexNamingNoSubobjectReturnsNullptr) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);  // index 0
  vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);             // index 0 within b

  int indices[] = {0, 99};  // b exists, b[99] does not
  EXPECT_EQ(vpi_handle_by_multi_index(mod, 2, indices), nullptr);
}

// §38.20: with no indices there is no index select expression to construct, so
// no subobject is named.
TEST_F(VpiHandleByMultiIndexSim, EmptyIndexListReturnsNullptr) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);

  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(mod, 0, indices), nullptr);
}

// §38.20: unless otherwise specified, calling vpi_handle_by_multi_index() for a
// protected reference object is an error - no handle is produced and the error
// status is recorded for vpi_chk_error() (§38.2).
TEST_F(VpiHandleByMultiIndexSim, ProtectedReferenceObjectIsAnError) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  mod->is_protected = true;

  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(mod, 1, indices), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

// §38.20: the reference object must carry the access-by-index property. A
// parameter offers no index-selected relationship, so even with a child at the
// requested index the routine builds no index select and returns null.
TEST_F(VpiHandleByMultiIndexSim, ReferenceWithoutAccessByIndexReturnsNullptr) {
  auto* param = vpi_ctx_.CreateParameter("p", 0);
  vpi_ctx_.CreatePort("a", kVpiInput, param);  // gives param a child at index 0

  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(param, 1, indices), nullptr);
}

}  // namespace
}  // namespace delta
