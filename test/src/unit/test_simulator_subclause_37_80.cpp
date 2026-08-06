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

// The diagram's four edges (prim term, expr, time queue, stmt -> callback): a
// callback placed on one of these objects is reached from that object by
// iterating vpiCallback with the object as the reference. The diagram depicts a
// data-model relationship (the callback's obj linkage), independent of the
// callback reason, so the kind of callback is immaterial here. Each helper
// builds an object of the diagram's kind, places a callback on it, and confirms
// the iteration hands that callback back.
namespace {
void ExpectCallbackReachedFromObject(int object_type) {
  VpiObject object;
  object.type = object_type;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = &object;
  vpiHandle registered = vpi_register_cb(&cb);
  ASSERT_NE(registered, nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, &object);
  ASSERT_NE(it, nullptr);
  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(reached->type, vpiCallback);
  EXPECT_EQ(reached, registered);
  EXPECT_EQ(vpi_scan(it), nullptr);
}
}  // namespace

TEST_F(Callback, CallbackOnPrimTermIsReachedFromPrimTerm) {
  ExpectCallbackReachedFromObject(vpiPrimTerm);
}

TEST_F(Callback, CallbackOnExprIsReachedFromExpr) {
  ExpectCallbackReachedFromObject(vpiOperation);
}

TEST_F(Callback, CallbackOnTimeQueueIsReachedFromTimeQueue) {
  ExpectCallbackReachedFromObject(vpiTimeQueue);
}

// The object-scoped iteration is limited to its reference object: a callback
// placed on one object is not reached from a different object, and a callback
// not related to any object (its obj field is null - detail 2) is not reached
// from an object reference either. The reference objects are statements, so
// this also observes the diagram's stmt -> callback edge on its positive path.
TEST_F(Callback, CallbackIterationFromObjectIsScopedToThatObject) {
  VpiObject target;
  target.type = vpiAssignStmt;
  VpiObject other;
  other.type = vpiAssignStmt;

  s_cb_data on_target = {};
  on_target.reason = cbValueChange;
  on_target.obj = &target;
  vpiHandle target_cb = vpi_register_cb(&on_target);
  ASSERT_NE(target_cb, nullptr);

  s_cb_data on_other = {};
  on_other.reason = cbValueChange;
  on_other.obj = &other;
  ASSERT_NE(vpi_register_cb(&on_other), nullptr);

  // A callback unrelated to any object must not surface from an object ref.
  s_cb_data unrelated = {};
  unrelated.reason = cbEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&unrelated), nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, &target);
  ASSERT_NE(it, nullptr);
  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(reached, target_cb);
  // Only the callback on the target is reached; the other object's callback and
  // the unrelated callback are not.
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// Edge case of the object -> callback edges: iterating vpiCallback from an
// object that carries no callback yields no iterator at all, even when
// callbacks are registered on other objects. The walk matches by the object a
// callback was placed on, so an object none name produces an empty result,
// which the iterate dispatch reports as a null handle rather than an empty
// iterator.
TEST_F(Callback, IterationFromObjectWithoutCallbackYieldsNoIterator) {
  VpiObject with_callback;
  with_callback.type = vpiAssignStmt;
  VpiObject without_callback;
  without_callback.type = vpiAssignStmt;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = &with_callback;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_iterate(vpiCallback, &without_callback), nullptr);
}

}  // namespace
}  // namespace delta
