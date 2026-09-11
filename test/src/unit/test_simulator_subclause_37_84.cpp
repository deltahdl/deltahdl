#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.84 Iterator: the object model diagram draws an iterator object that has a
// single scalar property and a single navigable edge.
//   -> type     int: vpiIteratorType
//   vpiUse ->   (instance array, scope, ports, nets, variables, processes,
//                statements, ... - the long catalog of objects an iterator may
//                have been created over)
// There is no BNF and no syntax in this clause; it owns the runtime behaviour
// of an iterator handle. Two normative pieces belong to it:
//   * the vpiIteratorType property - an iterator reports the kind of object it
//     walks (the type code handed to vpi_iterate); and
//   * the vpiUse relation, governed by details 1 and 2: vpi_handle(vpiUse, itr)
//     returns the reference handle the iterator was created over (detail 1), or
//     NULL when that reference was itself NULL (detail 2).
// These tests drive the production code through the public vpi_iterate,
// vpi_get, and vpi_handle entry points and observe each rule being applied.

// The fixture installs a context so the public entry points run their real
// dispatch over the test objects.
class Iterator : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Property (-> type, int: vpiIteratorType): an iterator reports the object kind
// its iteration walks. The kind is whatever type code created the iterator, so
// two iterators built over different types report their own type back - it is
// the stored argument, not a fixed constant. Both iterators are produced by the
// real vpi_iterate path so production stores the kind, and vpi_get reads it.
TEST_F(Iterator, IteratorTypeReportsTheWalkedKind) {
  VpiObject child_module;
  child_module.type = vpiModule;
  VpiObject child_port;
  child_port.type = vpiPort;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&child_module, &child_port};

  vpiHandle module_iter = vpi_iterate(vpiModule, &scope);
  ASSERT_NE(module_iter, nullptr);
  EXPECT_EQ(vpi_get(vpiIteratorType, module_iter), vpiModule);

  vpiHandle port_iter = vpi_iterate(vpiPort, &scope);
  ASSERT_NE(port_iter, nullptr);
  EXPECT_EQ(vpi_get(vpiIteratorType, port_iter), vpiPort);
}

// Edge (vpiUse), detail 1: vpi_handle(vpiUse, iterator) returns the reference
// handle the iterator was created over. The iterator here is produced by the
// real vpi_iterate path with a non-null reference, and vpiUse recovers exactly
// that reference object.
TEST_F(Iterator, UseRecoversTheReferenceHandle) {
  VpiObject child_module;
  child_module.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&child_module};

  vpiHandle iter = vpi_iterate(vpiModule, &scope);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_handle(vpiUse, iter), &scope);
}

// Edge (vpiUse), detail 2: an iterator may have been created over a NULL
// reference handle, in which case vpi_handle(vpiUse, iterator) returns NULL.
// The iterator is the one a real NULL-reference iteration hands back - §37.80
// detail 2's walk of the callbacks no object reaches - rather than an object
// built with the reference left unset, so what the detail is about is the
// iterator a caller can actually hold. It still reports the kind it walks.
TEST_F(Iterator, UseReturnsNullForAnIteratorCreatedOverANullReference) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpiHandle iter = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(iter, nullptr);

  EXPECT_EQ(vpi_handle(vpiUse, iter), nullptr);
  EXPECT_EQ(vpi_get(vpiIteratorType, iter), vpiCallback);
}

// Both the property and the edge are drawn on the iterator object alone. An
// object of another kind reports no iterator type, and vpiUse - which §37.58
// draws from a simple expression to the places it is used - does not hand back
// the reference of an iteration that object never was.
TEST_F(Iterator, TheTypeAndTheEdgeAreDrawnOnTheIteratorAlone) {
  VpiObject scope;
  scope.type = vpiModule;

  EXPECT_EQ(vpi_get(vpiIteratorType, &scope), vpiUndefined);
  EXPECT_EQ(vpi_handle(vpiUse, &scope), nullptr);
}

}  // namespace
}  // namespace delta
