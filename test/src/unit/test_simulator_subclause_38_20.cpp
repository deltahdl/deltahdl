#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

TEST_F(VpiHandleByMultiIndexSim, ResolvesNestedSubobjectFromIndexList) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  vpi_ctx_.CreatePort("a", kVpiInput, bus);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, bus);
  vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);
  auto* bit_b1 = vpi_ctx_.CreatePort("b1", kVpiOutput, port_b);

  int indices[] = {1, 1};
  vpiHandle result = vpi_handle_by_multi_index(VpiHandleOf(bus), 2, indices);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(VpiObjectOf(result), bit_b1);
}

TEST_F(VpiHandleByMultiIndexSim, IndicesAreAppliedLeftmostFirst) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  auto* port_a = vpi_ctx_.CreatePort("a", kVpiInput, bus);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, bus);
  vpi_ctx_.CreatePort("a0", kVpiInput, port_a);
  auto* a1 = vpi_ctx_.CreatePort("a1", kVpiInput, port_a);
  auto* b0 = vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);

  int forward[] = {0, 1};
  EXPECT_EQ(
      VpiObjectOf(vpi_handle_by_multi_index(VpiHandleOf(bus), 2, forward)), a1);

  int reversed[] = {1, 0};
  EXPECT_EQ(
      VpiObjectOf(vpi_handle_by_multi_index(VpiHandleOf(bus), 2, reversed)),
      b0);
}

TEST_F(VpiHandleByMultiIndexSim, NumIndexGovernsHowManyIndicesApply) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  vpi_ctx_.CreatePort("a", kVpiInput, bus);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, bus);
  vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);

  int indices[] = {1};
  EXPECT_EQ(
      VpiObjectOf(vpi_handle_by_multi_index(VpiHandleOf(bus), 1, indices)),
      port_b);
}

TEST_F(VpiHandleByMultiIndexSim, NullParentReturnsNullptr) {
  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(nullptr, 1, indices), nullptr);
}

TEST_F(VpiHandleByMultiIndexSim, IndexNamingNoSubobjectReturnsNullptr) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, bus);
  vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);

  int indices[] = {0, 99};
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 2, indices), nullptr);
}

TEST_F(VpiHandleByMultiIndexSim, EmptyIndexListReturnsNullptr) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  vpi_ctx_.CreatePort("a", kVpiInput, bus);

  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 0, indices), nullptr);
}

TEST_F(VpiHandleByMultiIndexSim, ProtectedReferenceObjectIsAnError) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  vpi_ctx_.CreatePort("a", kVpiInput, bus);
  bus->is_protected = true;

  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 1, indices), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

TEST_F(VpiHandleByMultiIndexSim, ReferenceWithoutAccessByIndexReturnsNullptr) {
  auto* param = vpi_ctx_.CreateParameter("p", 0);
  vpi_ctx_.CreatePort("a", kVpiInput, param);

  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(param), 1, indices), nullptr);
}

TEST_F(VpiHandleByMultiIndexSim, ANullIndexArrayNamesNothing) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 1, nullptr), nullptr);
}
}  // namespace
}  // namespace delta
