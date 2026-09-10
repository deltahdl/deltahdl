#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.2.3 (Handle comparison): "Handle equivalence cannot be determined with a
// C '==' comparison. The function vpi_compare_objects() compares the objects
// they refer to. It returns the value 1 if the objects they refer to are the
// same object); otherwise it returns the value 0."
//
// §37.2.1 is what makes that so: a tool "may create two distinct handles or may
// provide the same handle in both cases", so an application holding two handles
// to one object cannot tell from the pointers. What the clause asks of a tool
// is that it not make the same mistake: where the simulator itself asks whether
// two handles name one object, it has to ask §38.3's question rather than
// compare the pointers - and in two places it compared the pointers.
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

// §37.2.3: two distinct handles to one object are equivalent, and the routine
// that says so is the one the clause names - not the C comparison, which sees
// two different pointers.
TEST_F(VpiHandleComparison, DistinctHandlesToOneObjectAreEquivalent) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle other = ctx_.CreateHandleFor(mod);

  ASSERT_NE(mod, other);
  EXPECT_EQ(vpi_compare_objects(mod, other), 1);
}

// §37.2.3 applied to §37.80's callback iteration: a callback is placed on an
// object, so a second handle to that object reaches it. Deciding by pointer
// found the callback through the handle it was registered with and through no
// other.
TEST_F(VpiHandleComparison, ACallbackIsFoundThroughAnyHandleToItsObject) {
  VpiHandle mod = ctx_.CreateModule("top", "top");

  s_cb_data data = {};
  data.reason = cbValueChange;
  data.obj = mod;
  vpiHandle cb = vpi_register_cb(&data);
  ASSERT_NE(cb, nullptr);

  ASSERT_EQ(ScanAll(vpi_iterate(vpiCallback, mod)).size(), 1u);

  VpiHandle other = ctx_.CreateHandleFor(mod);
  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiCallback, other));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], cb);
}

// §37.2.3: the comparison is of objects, so a handle to a different object
// reaches none of the first object's callbacks.
TEST_F(VpiHandleComparison, ACallbackIsNotFoundThroughAnotherObject) {
  VpiHandle watched = ctx_.CreateModule("watched", "watched");
  VpiHandle unwatched = ctx_.CreateModule("unwatched", "unwatched");

  s_cb_data data = {};
  data.reason = cbValueChange;
  data.obj = watched;
  ASSERT_NE(vpi_register_cb(&data), nullptr);

  EXPECT_EQ(vpi_iterate(vpiCallback, unwatched), nullptr);
}

// §37.2.2 items 2 and 3 release "handles to callbacks placed on these objects",
// and §37.2.3 says which callbacks those are: the ones §38.3 calls placed on
// the object, whichever handle registered them.
TEST_F(VpiHandleComparison, ReleasingAnObjectReleasesItsCallbacksAnyHandle) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle other = ctx_.CreateHandleFor(mod);

  s_cb_data data = {};
  data.reason = cbValueChange;
  data.obj = other;  // registered through the second handle
  vpiHandle cb = vpi_register_cb(&data);
  ASSERT_NE(cb, nullptr);
  ASSERT_FALSE(cb->released);

  ctx_.ReleaseFrameOrThreadObject(mod);

  EXPECT_TRUE(mod->released);
  EXPECT_TRUE(cb->released);
}

}  // namespace
}  // namespace delta
