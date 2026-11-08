#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

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

TEST(ObtainAssertionHandles, NullReferenceWalksEveryAssertionInDesign) {
  VpiContext ctx;
  VpiHandle a = ctx.CreateAssertion("a_req", vpiAssert);
  VpiHandle c = ctx.CreateAssertion("c_cov", vpiCover);
  ctx.CreateParameter("WIDTH", 8);

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], a);
  EXPECT_EQ(seen[1], c);
}

TEST(ObtainAssertionHandles, InstanceReferenceWalksOnlyThatInstance) {
  VpiContext ctx;

  VpiObject dut;
  dut.type = vpiModule;
  VpiObject in_dut;
  in_dut.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
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

TEST(ObtainAssertionHandles, HandleByNameAnswersTheAssertionItsLabelWraps) {
  VpiContext ctx;
  VpiObject root;
  root.type = vpiModule;
  VpiObject begin;
  begin.type = vpiNamedBegin;
  begin.name = "i1";
  begin.full_name = "top.i1";
  VpiObject assertion;
  assertion.type = vpiImmediateAssert;
  assertion.name = "i1";
  assertion.full_name = "top.i1";
  begin.children = {&assertion};
  root.children = {&begin};

  EXPECT_EQ(ctx.HandleByName("i1", &root), &assertion);
}

TEST(ObtainAssertionHandles, HandleByNameAnswersABeginHoldingAnUnnamedOne) {
  VpiContext ctx;
  VpiObject root;
  root.type = vpiModule;
  VpiObject begin;
  begin.type = vpiNamedBegin;
  begin.name = "b";
  begin.full_name = "top.b";
  VpiObject statement;
  statement.type = vpiAssignment;
  VpiObject unnamed;
  unnamed.type = vpiImmediateAssert;
  begin.children = {&statement, &unnamed};
  root.children = {&begin};

  EXPECT_EQ(ctx.HandleByName("b", &root), &begin);
}

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

TEST(ObtainAssertionHandles, UnnamedAssertionCannotBeFoundByName) {
  VpiContext ctx;
  VpiHandle named = ctx.CreateAssertion("named_p", vpiAssert);
  VpiHandle unnamed = ctx.CreateAssertion("", vpiCover);

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);
  EXPECT_NE(std::find(seen.begin(), seen.end(), unnamed), seen.end());

  EXPECT_EQ(ctx.HandleByName("named_p", nullptr), named);
  EXPECT_EQ(ctx.HandleByName("", nullptr), nullptr);
}

TEST(ObtainAssertionHandles, InstanceWalkReachesAssertionsInsideItsBlocks) {
  VpiContext ctx;
  VpiObject dut;
  dut.type = vpiModule;

  VpiObject at_the_top;
  at_the_top.type = vpiAssert;
  VpiObject block;
  block.type = vpiNamedBegin;
  VpiObject in_the_block;
  in_the_block.type = vpiCover;
  VpiObject deeper;
  deeper.type = vpiAlways;
  VpiObject in_the_procedure;
  in_the_procedure.type = vpiImmediateAssert;

  deeper.children = {&in_the_procedure};
  block.children = {&in_the_block, &deeper};
  dut.children = {&at_the_top, &block};

  VpiHandle it = ctx.Iterate(vpiAssertion, &dut);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  EXPECT_EQ(seen.size(), 3u);
  EXPECT_NE(std::find(seen.begin(), seen.end(), &at_the_top), seen.end());
  EXPECT_NE(std::find(seen.begin(), seen.end(), &in_the_block), seen.end());
  EXPECT_NE(std::find(seen.begin(), seen.end(), &in_the_procedure), seen.end());
  EXPECT_EQ(std::find(seen.begin(), seen.end(), &block), seen.end());
}

TEST(ObtainAssertionHandles, InstanceWalkStopsAtAnInstanceNestedInside) {
  VpiContext ctx;
  VpiObject dut;
  dut.type = vpiModule;
  VpiObject own;
  own.type = vpiAssert;
  VpiObject sub;
  sub.type = vpiModule;
  VpiObject in_sub;
  in_sub.type = vpiAssert;
  sub.children = {&in_sub};
  dut.children = {&own, &sub};

  VpiHandle it = ctx.Iterate(vpiAssertion, &dut);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &own);

  VpiHandle sub_it = ctx.Iterate(vpiAssertion, &sub);
  ASSERT_NE(sub_it, nullptr);
  EXPECT_EQ(ctx.Scan(sub_it), &in_sub);
  EXPECT_EQ(ctx.Scan(sub_it), nullptr);
}

}  // namespace
}  // namespace delta
