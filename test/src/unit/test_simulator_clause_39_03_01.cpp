#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §39.3.1 "Obtaining assertion handles" describes how a VPI application reaches
// the handle for a named assertion through direct access. It carries no BNF and
// no "shall" sentences; its normative content is the navigation recipe and two
// closing details:
//   - the VPI navigation/instance-iterator model reaches assertions,
//   properties,
//     and sequences (intro);
//   - (a) a null reference to vpi_iterate(vpiAssertion, ...) walks every
//     assertion in the design;
//   - (b) an instance reference to vpi_iterate(vpiAssertion, ...) walks the
//     assertions of just that instance;
//   - (c) vpi_handle_by_name() also resolves assertion names in scope;
//   - (d) a specific assertion kind is selected by filtering the walk on
//     vpi_get(vpiType, assertion);
//   - an assertion handle denotes one specific assertion in one specific
//     instance;
//   - an unnamed assertion cannot be found by name.
// The object model, class grouping, name resolution, and vpi_get(vpiType)
// machinery these steps drive are owned by §37.49/§37.50/§37.51/§38.21; these
// tests observe that production machinery applying the §39.3.1 recipe.

// Intro: the assertion-class walk reaches not only assertion directives but the
// property and sequence instances the navigation model encompasses.
TEST(ObtainAssertionHandles,
     NavigationEncompassesAssertionsPropertiesSequences) {
  VpiContext ctx;
  VpiHandle assertion = ctx.CreateAssertion("a_req", vpiAssert);
  VpiHandle property = ctx.CreateAssertion("p_inst", vpiPropertyInst);
  VpiHandle sequence = ctx.CreateAssertion("s_inst", vpiSequenceInst);

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  EXPECT_EQ(seen.size(), 3u);
  EXPECT_NE(std::find(seen.begin(), seen.end(), assertion), seen.end());
  EXPECT_NE(std::find(seen.begin(), seen.end(), property), seen.end());
  EXPECT_NE(std::find(seen.begin(), seen.end(), sequence), seen.end());
}

// Step a: a null reference handle to vpi_iterate(vpiAssertion, ...) returns
// every assertion in the design and skips non-assertion objects.
TEST(ObtainAssertionHandles, NullReferenceWalksEveryAssertionInDesign) {
  VpiContext ctx;
  VpiHandle a = ctx.CreateAssertion("a_req", vpiAssert);
  VpiHandle c = ctx.CreateAssertion("c_cov", vpiCover);
  ctx.CreateParameter("WIDTH", 8);  // not an assertion

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], a);
  EXPECT_EQ(seen[1], c);
}

// Step b: passing an instance handle as the reference confines the walk to the
// assertions written in that instance; assertions in another instance are not
// returned.
TEST(ObtainAssertionHandles, InstanceReferenceWalksOnlyThatInstance) {
  VpiContext ctx;

  VpiObject dut;
  dut.type = vpiModule;
  VpiObject in_dut;
  in_dut.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;  // a non-assertion member is skipped
  dut.children = {&net_child, &in_dut};

  VpiObject other;
  other.type = vpiModule;
  VpiObject in_other;
  in_other.type = vpiCover;
  other.children = {&in_other};

  VpiHandle it = ctx.Iterate(vpiAssertion, &dut);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &in_dut);
  EXPECT_EQ(std::find(seen.begin(), seen.end(), &in_other), seen.end());
}

// Step c: vpi_handle_by_name() resolves an assertion name. A named assertion
// registered at the top level is returned for that name; within a scope the
// search is confined to that scope.
TEST(ObtainAssertionHandles, HandleByNameResolvesAssertionName) {
  VpiContext ctx;
  VpiHandle top = ctx.CreateAssertion("handshake_p", vpiAssert);

  EXPECT_EQ(ctx.HandleByName("handshake_p", nullptr), top);
  EXPECT_EQ(ctx.HandleByName("no_such_assertion", nullptr), nullptr);

  VpiObject scope;
  scope.type = vpiModule;
  VpiObject scoped;
  scoped.type = vpiCover;
  scoped.name = "branch_c";
  scope.children = {&scoped};

  EXPECT_EQ(ctx.HandleByName("branch_c", &scope), &scoped);
}

// Step c edge: an assertion is reachable by a hierarchical name, the search
// descending through the named scope(s) to the assertion leaf. A path whose
// final component names nothing resolves to no handle.
TEST(ObtainAssertionHandles, HandleByNameResolvesAssertionInNestedScope) {
  VpiContext ctx;
  VpiObject root;
  root.type = vpiModule;
  VpiObject dut;
  dut.type = vpiModule;
  dut.name = "dut";
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.name = "branch_c";
  dut.children = {&assertion};
  root.children = {&dut};

  EXPECT_EQ(ctx.HandleByName("dut.branch_c", &root), &assertion);
  EXPECT_EQ(ctx.HandleByName("dut.absent_p", &root), nullptr);
}

// Step d: an assertion of a specific kind is obtained by walking the assertion
// class and keeping the handles whose vpi_get(vpiType) equals the wanted kind
// (here vpiCover), as the LRM's concurrent cover example shows.
TEST(ObtainAssertionHandles, FilterWalkByVpiTypeSelectsSpecificKind) {
  VpiContext ctx;
  ctx.CreateAssertion("a_req", vpiAssert);
  VpiHandle cover = ctx.CreateAssertion("c_cov", vpiCover);
  ctx.CreateAssertion("m_asm", vpiAssume);

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> covers;
  while (VpiHandle h = ctx.Scan(it)) {
    if (ctx.Get(vpiType, h) == vpiCover) covers.push_back(h);
  }

  ASSERT_EQ(covers.size(), 1u);
  EXPECT_EQ(covers[0], cover);
}

// Step d edge: when the design holds no assertion of the wanted kind, filtering
// the assertion-class walk on vpi_get(vpiType) yields no handle — a specific
// type cannot be obtained when none of that type exists.
TEST(ObtainAssertionHandles, FilterWalkFindsNoHandleWhenKindAbsent) {
  VpiContext ctx;
  ctx.CreateAssertion("a_req", vpiAssert);
  ctx.CreateAssertion("m_asm", vpiAssume);

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> covers;
  while (VpiHandle h = ctx.Scan(it)) {
    if (ctx.Get(vpiType, h) == vpiCover) covers.push_back(h);
  }

  EXPECT_TRUE(covers.empty());
}

// Detail: an assertion handle denotes one specific assertion in one specific
// instance. Two assertions, even of the same kind, are distinct handles and
// each reports its own identity through vpi_get(vpiType).
TEST(ObtainAssertionHandles, EachHandleDenotesOneSpecificAssertion) {
  VpiContext ctx;
  VpiHandle first = ctx.CreateAssertion("a_req", vpiAssert);
  VpiHandle second = ctx.CreateAssertion("b_req", vpiAssert);

  EXPECT_NE(first, second);
  EXPECT_EQ(ctx.HandleByName("a_req", nullptr), first);
  EXPECT_EQ(ctx.HandleByName("b_req", nullptr), second);
  EXPECT_EQ(ctx.Get(vpiType, first), vpiAssert);
  EXPECT_EQ(ctx.Get(vpiType, second), vpiAssert);
}

// Detail: an unnamed assertion cannot be found by name even though it exists in
// the design and is reachable by iteration. Creating it with no name leaves it
// out of the by-name lookup, so vpi_handle_by_name() returns no handle.
TEST(ObtainAssertionHandles, UnnamedAssertionCannotBeFoundByName) {
  VpiContext ctx;
  VpiHandle named = ctx.CreateAssertion("named_p", vpiAssert);
  VpiHandle unnamed = ctx.CreateAssertion("", vpiCover);

  // It exists in the design: the null-reference walk reaches both.
  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);
  EXPECT_NE(std::find(seen.begin(), seen.end(), unnamed), seen.end());

  // But it is unreachable by name, while the named one resolves.
  EXPECT_EQ(ctx.HandleByName("named_p", nullptr), named);
  EXPECT_EQ(ctx.HandleByName("", nullptr), nullptr);
}

}  // namespace
}  // namespace delta
