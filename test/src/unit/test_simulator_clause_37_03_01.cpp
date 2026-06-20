#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <type_traits>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.1 (Accessing object relationships and properties) states the access
// conventions every VPI program relies on. It introduces no BNF; its normative
// content is a set of cross-cutting type and representation contracts plus the
// two traversal mechanisms, all of which the existing simulator C-ABI already
// applies (the routines themselves being described in Clause 38). These tests
// observe the production routines vpi_get(), vpi_get_str(), vpi_handle(), and
// vpi_iterate()/vpi_scan() honoring those conventions.
//
// Each test drives a private VpiContext through the public C entry points by
// installing it as the global context, exactly as a PLI program would reach the
// routines.
class VpiObjectAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// Claim: integer and Boolean properties shall be derived with the vpi_get
// family, and they shall be of type PLI_INT32. vpi_get() carries that contract:
// its result type is the 32-bit integer alias, and it returns the stored
// integer value of an integer-valued property.
TEST_F(VpiObjectAccess, GetDerivesIntegerPropertiesAsPliInt32) {
  static_assert(std::is_same_v<decltype(vpi_get(0, nullptr)), int>,
                "vpi_get must return the integer property type");
  static_assert(std::is_same_v<PLI_INT32, std::int32_t>,
                "integer/Boolean properties are PLI_INT32");

  VpiObject net;
  net.type = vpiNet;
  net.size = 8;

  EXPECT_EQ(vpi_get(vpiSize, &net), 8);
}

// Claim: for a Boolean property, a value of 1 shall represent TRUE and a value
// of 0 shall represent FALSE. vpi_get() of any Boolean property yields exactly
// one of those two values - never the raw stored object state.
TEST_F(VpiObjectAccess, GetEncodesBooleanPropertiesAsOneOrZero) {
  VpiObject active_thread;
  active_thread.type = vpiThread;
  active_thread.active = true;
  EXPECT_EQ(vpi_get(vpiActive, &active_thread), 1);

  VpiObject idle_thread;
  idle_thread.type = vpiThread;
  idle_thread.active = false;
  EXPECT_EQ(vpi_get(vpiActive, &idle_thread), 0);
}

// Claim: string properties shall be accessed with vpi_get_str() and shall be of
// type PLI_BYTE8 *. The example retrieves the full hierarchical name, so the
// result points at that name string.
TEST_F(VpiObjectAccess, GetStrAccessesStringPropertiesAsPliByte8) {
  static_assert(std::is_same_v<PLI_BYTE8, char>,
                "string properties are PLI_BYTE8 *");

  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "m1";
  mod.full_name = "top.m1";

  const char* full_name = vpi_get_str(vpiFullName, &mod);
  ASSERT_NE(full_name, nullptr);
  EXPECT_EQ(std::string(full_name), "top.m1");
}

// Claim: one-to-one relationships are traversed with vpi_handle(), which
// returns a handle to the related object - the example walks from a net to the
// module that contains it. The result is itself a vpiHandle.
TEST_F(VpiObjectAccess, HandleTraversesOneToOneRelationship) {
  static_assert(std::is_same_v<decltype(VpiHandleC(0, nullptr)), vpiHandle>,
                "vpi_handle returns a vpiHandle");

  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "m1";

  VpiObject net;
  net.type = vpiNet;
  net.parent = &mod;

  EXPECT_EQ(VpiHandleC(vpiModule, &net), &mod);
}

// Claim: one-to-many relationships are traversed with an iteration mechanism -
// vpi_iterate() creates an object of type vpiIterator, which vpi_scan() then
// walks one related object at a time. Here the nets contained in a module are
// enumerated.
TEST_F(VpiObjectAccess, IterateAndScanTraverseOneToManyRelationship) {
  VpiObject mod;
  mod.type = vpiModule;

  VpiObject w1;
  w1.type = vpiNet;
  w1.name = "w1";
  VpiObject w2;
  w2.type = vpiNet;
  w2.name = "w2";
  mod.children.push_back(&w1);
  mod.children.push_back(&w2);

  vpiHandle iter = vpi_iterate(vpiNet, &mod);
  ASSERT_NE(iter, nullptr);
  // The created object's own type is vpiIterator (the requested type only
  // selects which related objects it walks).
  EXPECT_EQ(vpi_get(vpiType, iter), vpiIterator);

  EXPECT_EQ(vpi_scan(iter), &w1);
  EXPECT_EQ(vpi_scan(iter), &w2);
  // Exhausting the iteration reports null and retires the iterator handle.
  EXPECT_EQ(vpi_scan(iter), nullptr);
}

// Edge of the Boolean-property rule: the 1/0 representation is general, not
// tied to one property. It holds for a property derived by computation
// (vpiExpanded, reported as the negation of the vectored flag) and for one read
// straight from a stored flag (vpiExplicitScalared) - in every case vpi_get()
// yields only 1 or 0.
TEST_F(VpiObjectAccess, GetEncodesEveryBooleanPropertyAsOneOrZero) {
  VpiObject vectored_net;
  vectored_net.type = vpiNet;
  vectored_net.is_vectored = true;
  // A derived Boolean: a vectored net is reported unexpanded (FALSE -> 0).
  EXPECT_EQ(vpi_get(vpiExpanded, &vectored_net), 0);

  VpiObject plain_net;
  plain_net.type = vpiNet;
  // The same derived Boolean is TRUE -> 1 for a net with no vector keyword.
  EXPECT_EQ(vpi_get(vpiExpanded, &plain_net), 1);

  VpiObject scalared_net;
  scalared_net.type = vpiNet;
  scalared_net.is_scalared = true;
  // A stored Boolean: TRUE -> 1, FALSE -> 0.
  EXPECT_EQ(vpi_get(vpiExplicitScalared, &scalared_net), 1);
  EXPECT_EQ(vpi_get(vpiExplicitScalared, &plain_net), 0);
}

// Edge of the string-property rule: vpi_get_str() accesses string properties
// other than the full name (here the simple name), and when an object carries
// no distinct full hierarchical name the full-name query falls back to that
// simple name. Both still hand back a PLI_BYTE8 * string.
TEST_F(VpiObjectAccess, GetStrAccessesNamePropertyAndFullNameFallback) {
  VpiObject net;
  net.type = vpiNet;
  net.name = "w1";  // no separate full_name stored

  const char* name = vpi_get_str(vpiName, &net);
  ASSERT_NE(name, nullptr);
  EXPECT_EQ(std::string(name), "w1");

  const char* full_name = vpi_get_str(vpiFullName, &net);
  ASSERT_NE(full_name, nullptr);
  EXPECT_EQ(std::string(full_name), "w1");
}

// Edge of the one-to-one traversal rule: when the reference object has no such
// relationship, vpi_handle() produces no handle. A net with no containing
// module and no children yields a null handle for the vpiModule relation.
TEST_F(VpiObjectAccess, HandleReturnsNoHandleForAbsentRelationship) {
  VpiObject net;
  net.type = vpiNet;

  EXPECT_EQ(VpiHandleC(vpiModule, &net), nullptr);
}

}  // namespace
}  // namespace delta
