#include <gtest/gtest.h>

#include <array>
#include <cstddef>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.80 Callback: the object model diagram for the VPI callback object. It
// draws two arrows into `callback` and they differ in their heads, which
// §37.4.3 makes the difference between the two routines. A prim term, an expr,
// a time queue and a stmt each reach one through a single arrow - a
// vpi_handle(vpiCallback, obj), the callback that object was given - and a
// circle reaches one through a double arrow, which is the vpi_iterate(...,
// NULL) form. The callback's own "cb info" relation is read with
// vpi_get_cb_info() (§38.8). The clause carries no BNF and no 'shall' BNF
// productions. Its two numbered details are:
//   1) vpi_get_cb_info() can be used to read a callback object's information -
//      a descriptive note delegating to the §38.8 routine;
//   2) callback objects not related to the diagram's objects are reached by
//      passing NULL as the second argument to vpi_iterate() - the lone 'shall'.
//
// A callback object is held in the run's callback registry rather than among
// the children of the object it was placed on, so the walk that serves an
// untagged relation - looking for a child whose own type is the relation's -
// reached none, and the single arrow the four objects draw was answered by
// nothing at all. Detail 2's NULL form went the other way and handed back every
// callback the run held, the ones those four objects reach included, so the
// iteration the detail defines for the rest was the whole registry. These tests
// drive both forms through the public vpi_handle / vpi_iterate / vpi_scan
// dispatch, and confirm the diagram's callback -> cb info edge through
// vpi_get_cb_info on a reached callback.

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

// The diagram's four single arrows (prim term, expr, time queue, stmt ->
// callback): a callback placed on one of these objects is reached from that
// object through vpi_handle(vpiCallback, obj), and from it by the iteration
// that walks the registry as well. The diagram depicts a data-model
// relationship (the callback's obj linkage), independent of the callback
// reason, so the kind of callback is immaterial here. Each helper builds an
// object of the diagram's kind, places a callback on it, and confirms both
// forms hand that callback back - and that the NULL-reference iteration, which
// detail 2 gives the callbacks not related to these objects, does not.
namespace {
void ExpectCallbackReachedFromObject(int object_type) {
  VpiObject object;
  object.type = object_type;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = &object;
  vpiHandle registered = vpi_register_cb(&cb);
  ASSERT_NE(registered, nullptr);

  EXPECT_EQ(vpi_handle(vpiCallback, &object), registered);

  vpiHandle it = vpi_iterate(vpiCallback, &object);
  ASSERT_NE(it, nullptr);
  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(reached->type, vpiCallback);
  EXPECT_EQ(reached, registered);
  EXPECT_EQ(vpi_scan(it), nullptr);

  // Detail 2: this callback is related to one of the diagram's objects, so the
  // NULL-reference iteration is not where it is found.
  EXPECT_EQ(vpi_iterate(vpiCallback, nullptr), nullptr);
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

// The single arrow is drawn from four kinds, and the `expr` and `stmt` ones are
// classes: §37.4.1 makes a dotted enclosure a grouping, so every kind §37.59
// draws in `expr` and every kind the `stmt` class groups is an object the
// arrow is drawn from.
TEST_F(Callback, TheSingleArrowIsDrawnFromEveryKindTheTwoClassesGroup) {
  constexpr std::array<int, 8> kHostKinds = {
      vpiPrimTerm, vpiTimeQueue, vpiOperation,  vpiConstant,
      vpiRefObj,   vpiBegin,     vpiAssignment, vpiForever};
  // The objects outlive the registrations, which record the address of the one
  // a callback was placed on; a fresh object per iteration would take the same
  // storage as the last and every callback would name it.
  std::array<VpiObject, kHostKinds.size()> objects;
  std::array<vpiHandle, kHostKinds.size()> registered = {};

  for (size_t i = 0; i < kHostKinds.size(); ++i) {
    objects[i].type = kHostKinds[i];

    s_cb_data cb = {};
    cb.reason = cbValueChange;
    cb.obj = &objects[i];
    registered[i] = vpi_register_cb(&cb);
    ASSERT_NE(registered[i], nullptr) << "host kind " << kHostKinds[i];
  }

  for (size_t i = 0; i < kHostKinds.size(); ++i) {
    EXPECT_EQ(vpi_handle(vpiCallback, &objects[i]), registered[i])
        << "host kind " << kHostKinds[i];
  }
}

// The single arrow reaches nothing where the object was given no callback, and
// the relation is not read off an object of a kind the arrow is not drawn from:
// a module holds callbacks like any other object, but the diagram draws no
// arrow from one, so vpi_handle reports none there.
TEST_F(Callback, TheSingleArrowReachesNothingWhereTheDiagramDrawsNone) {
  VpiObject without_callback;
  without_callback.type = vpiAssignStmt;
  EXPECT_EQ(vpi_handle(vpiCallback, &without_callback), nullptr);

  VpiObject module;
  module.type = vpiModule;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = &module;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_handle(vpiCallback, &module), nullptr);
}

// Detail 2: "To get callback objects not related to the above objects, the
// second argument to vpi_iterate() shall be NULL." So the NULL form hands back
// the callbacks the diagram's single arrow leaves unreachable - one placed on
// no object, and one placed on an object of a kind that arrow is not drawn from
// - and not the ones a prim term, an expr, a time queue or a stmt reaches.
TEST_F(Callback, NullReferenceIterationReachesOnlyTheUnrelatedCallbacks) {
  VpiObject statement;
  statement.type = vpiAssignStmt;
  VpiObject module;
  module.type = vpiModule;

  s_cb_data on_stmt = {};
  on_stmt.reason = cbValueChange;
  on_stmt.obj = &statement;
  vpiHandle stmt_cb = vpi_register_cb(&on_stmt);
  ASSERT_NE(stmt_cb, nullptr);

  s_cb_data on_module = {};
  on_module.reason = cbValueChange;
  on_module.obj = &module;
  vpiHandle module_cb = vpi_register_cb(&on_module);
  ASSERT_NE(module_cb, nullptr);

  s_cb_data on_nothing = {};
  on_nothing.reason = cbEndOfSimulation;
  vpiHandle free_cb = vpi_register_cb(&on_nothing);
  ASSERT_NE(free_cb, nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), module_cb);
  EXPECT_EQ(vpi_scan(it), free_cb);
  EXPECT_EQ(vpi_scan(it), nullptr);  // the statement's callback is not here

  // It is reached from the statement instead, which is the arrow the diagram
  // does draw.
  EXPECT_EQ(vpi_handle(vpiCallback, &statement), stmt_cb);
}

// §37.2.2 has vpi_remove_cb() release the callback's handle, so the object that
// reached it through the diagram's single arrow reaches it no longer: the
// relation reports none rather than a handle to an object the run has let go.
TEST_F(Callback, TheSingleArrowReachesNothingOnceTheCallbackIsRemoved) {
  VpiObject statement;
  statement.type = vpiAssignStmt;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = &statement;
  vpiHandle registered = vpi_register_cb(&cb);
  ASSERT_NE(registered, nullptr);
  ASSERT_EQ(vpi_handle(vpiCallback, &statement), registered);

  EXPECT_EQ(vpi_remove_cb(registered), 1);
  EXPECT_EQ(vpi_handle(vpiCallback, &statement), nullptr);
}

}  // namespace
}  // namespace delta
