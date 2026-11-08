#include <gtest/gtest.h>

#include <vector>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleComparison : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

TEST_F(VpiHandleComparison, DistinctHandlesToOneObjectAreEquivalent) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle other = ctx_.CreateHandleFor(mod);

  ASSERT_NE(mod, other);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(mod), VpiHandleOf(other)), 1);
}

TEST_F(VpiHandleComparison, ACallbackIsFoundThroughAnyHandleToItsObject) {
  VpiHandle mod = ctx_.CreateModule("top", "top");

  s_cb_data data = {};
  data.reason = cbValueChange;
  data.obj = VpiHandleOf(mod);
  vpiHandle cb = vpi_register_cb(&data);
  ASSERT_NE(cb, nullptr);

  ASSERT_EQ(ScanAll(vpi_iterate(vpiCallback, VpiHandleOf(mod))).size(), 1u);

  VpiHandle other = ctx_.CreateHandleFor(mod);
  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiCallback, VpiHandleOf(other)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], cb);
}

TEST_F(VpiHandleComparison, ACallbackIsNotFoundThroughAnotherObject) {
  VpiHandle watched = ctx_.CreateModule("watched", "watched");
  VpiHandle unwatched = ctx_.CreateModule("unwatched", "unwatched");

  s_cb_data data = {};
  data.reason = cbValueChange;
  data.obj = VpiHandleOf(watched);
  ASSERT_NE(vpi_register_cb(&data), nullptr);

  EXPECT_EQ(vpi_iterate(vpiCallback, VpiHandleOf(unwatched)), nullptr);
}

TEST_F(VpiHandleComparison, ReleasingAnObjectReleasesItsCallbacksAnyHandle) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle other = ctx_.CreateHandleFor(mod);

  s_cb_data data = {};
  data.reason = cbValueChange;
  data.obj = VpiHandleOf(other);
  vpiHandle cb = vpi_register_cb(&data);
  ASSERT_NE(cb, nullptr);
  ASSERT_FALSE(VpiObjectOf(cb)->released);

  ctx_.ReleaseFrameOrThreadObject(mod);

  EXPECT_TRUE(mod->released);
  EXPECT_TRUE(VpiObjectOf(cb)->released);
}

}  // namespace
}  // namespace delta
