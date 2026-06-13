#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.80 Callback: the object model diagram for the VPI callback object. A
// circle reaches a "callback" object, which is also reached from a prim term,
// an expr, a time queue, and a stmt; the callback's own "cb info" relation is
// read with vpi_get_cb_info() (§38.8). The clause carries no BNF and no 'shall'
// BNF productions. Its two numbered details are:
//   1) vpi_get_cb_info() can be used to read a callback object's information -
//      a descriptive note delegating to the §38.8 routine;
//   2) callback objects not related to the diagram's objects are reached by
//      passing NULL as the second argument to vpi_iterate() - the lone 'shall'.
// Detail 2 is applied by the production NULL-reference iteration walk, which
// hands back every registered callback object when no reference object scopes
// the iteration. These tests drive that walk through the public vpi_iterate /
// vpi_scan dispatch, and confirm the diagram's callback -> cb info edge through
// vpi_get_cb_info on an iterated callback.

// The fixture installs a context so the public entry points run their real
// dispatch over the callbacks registered in the test.
class Callback : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Detail 2: a callback registered without being scoped to one of the diagram's
// objects is reached by iterating vpiCallback with a NULL reference object. The
// walk hands back the registered callback, and the scanned object is itself a
// vpiCallback.
TEST_F(Callback, NullReferenceIterationReachesRegisteredCallback) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle registered = vpi_register_cb(&cb);
  ASSERT_NE(registered, nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(it, nullptr);

  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(reached->type, vpiCallback);
  EXPECT_EQ(reached, registered);

  // Exactly one callback was registered, so the next scan retires the iterator.
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// Detail 1 / the callback -> cb info edge: a callback object reached by the
// iteration carries the information vpi_get_cb_info() reports, so reading the
// iterated handle's cb info hands back the reason it was registered with.
TEST_F(Callback, CallbackInfoIsReadableFromIteratedCallback) {
  s_cb_data cb = {};
  cb.reason = cbStartOfSimulation;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(it, nullptr);
  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);

  s_cb_data info = {};
  vpi_get_cb_info(reached, &info);
  EXPECT_EQ(info.reason, cbStartOfSimulation);
}

}  // namespace
}  // namespace delta
