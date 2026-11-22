#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_assertion_sites.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
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

class AssertionHandlesOfARun : public VpiDesignRun {
 protected:
  static int KindOf(const char* scope, const char* name) {
    vpiHandle assertion = Named(vpiAssertion, By(scope), name);
    return assertion == nullptr ? 0 : vpi_get(vpiType, assertion);
  }
};

int CountOf(const std::vector<std::string>& names, const char* name) {
  return static_cast<int>(std::ranges::count(names, name));
}

TEST_F(AssertionHandlesOfARun, AnInstanceWalkReachesItsGenerateBlocks) {
  Run(kAssertionSites);
  const std::vector<std::string> kNames = AssertionFullNamesUnder(By("top"));
  EXPECT_EQ(CountOf(kNames, "top.g[0].ag"), 1);
  EXPECT_EQ(CountOf(kNames, "top.g[1].ag"), 1);
}

TEST_F(AssertionHandlesOfARun, AnInstanceWalkSkipsTheInstancesNestedInIt) {
  Run(kAssertionSites);
  const std::vector<std::string> kNames = AssertionFullNamesUnder(By("top"));
  for (const char* name :
       {"top.u1.as", "top.u1.sg.sg1", "top.u2.as", "top.b.ai", "top.p.ap"}) {
    EXPECT_EQ(CountOf(kNames, name), 0) << name;
  }
  EXPECT_EQ(CountOf(kNames, "top.am"), 1);
  EXPECT_EQ(CountOf(kNames, "top.pc"), 1);
}

TEST_F(AssertionHandlesOfARun, AnInterfaceAndAProgramWalkReachTheirOwn) {
  Run(kAssertionSites);
  EXPECT_EQ(AssertionFullNamesUnder(By("top.b")),
            (std::vector<std::string>{"top.b.ai"}));
  EXPECT_EQ(AssertionFullNamesUnder(By("top.p")),
            (std::vector<std::string>{"top.p.ap"}));
}

TEST_F(AssertionHandlesOfARun, AWalkOfOneInstanceSkipsItsSibling) {
  Run(kAssertionSites);
  EXPECT_EQ(AssertionFullNamesUnder(By("top.u1")),
            (std::vector<std::string>{"top.u1.as", "top.u1.sg.sg1"}));
  EXPECT_EQ(AssertionFullNamesUnder(By("top.u2")),
            (std::vector<std::string>{"top.u2.as", "top.u2.sg.sg1"}));
}

TEST_F(AssertionHandlesOfARun,
       DISABLED_ACheckersAssertionIsItsEnclosingInstances) {
  Run(kAssertionSites);
  EXPECT_NE(Named(vpiAssertion, By("top"), "ac"), nullptr);
}

TEST_F(AssertionHandlesOfARun, AWalkOfACheckerInstanceReachesItsAssertion) {
  Run(kAssertionSites);
  EXPECT_EQ(AssertionFullNamesUnder(By("top.k")),
            (std::vector<std::string>{"top.k.ac"}));
}

TEST_F(AssertionHandlesOfARun,
       DISABLED_AWalkOfAnInstanceHoldingAGateReachesItsAssertion) {
  Run("module top; logic clk, x; wire w, a, b;\n"
      "  and g (w, a, b);\n"
      "  a1: assert property (@(posedge clk) x);\n"
      "endmodule\n");
  EXPECT_EQ(AssertionFullNamesUnder(By("top")),
            (std::vector<std::string>{"top.a1"}));
}

TEST_F(AssertionHandlesOfARun, ANullWalkReachesEachAssertionOfTheDesignOnce) {
  Run(kAssertionSites);
  const std::vector<std::string> kNames = AssertionFullNamesUnder(nullptr);
  for (const char* name :
       {"top.am", "top.d0", "top.pc", "top.ad", "top.df", "top.g[1].ag",
        "top.u1.as", "top.u2.as", "top.u1.sg.sg1", "top.b.ai", "top.p.ap",
        "top.k.ac", "top.aa"}) {
    EXPECT_EQ(CountOf(kNames, name), 1) << name;
  }
  for (const char* name : {"top.a", "top.clk", "top.n", "top.P"}) {
    EXPECT_EQ(CountOf(kNames, name), 0) << name;
  }
}

TEST_F(AssertionHandlesOfARun, AnUnlabelledAssertionIsWalkedNeverFoundByName) {
  Run("module top; logic clk, a;\n"
      "  assert property (@(posedge clk) a);\n"
      "  assert #0 (a);\n"
      "  always @(posedge clk) assert property (a);\n"
      "  initial begin assert (a); assert final (a); end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  std::vector<int> kinds = KindsOf(vpiAssertion, top);
  std::vector<int> expected = {vpiAssert, vpiAssert, vpiImmediateAssert,
                               vpiImmediateAssert, vpiImmediateAssert};
  std::ranges::sort(kinds);
  std::ranges::sort(expected);
  EXPECT_EQ(kinds, expected);
  EXPECT_EQ(vpi_handle_by_name(VpiText(""), top), nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_name(VpiText("top"), nullptr)),
            vpiModule);
  for (vpiHandle assertion : ObjectsOf(vpiAssertion, top)) {
    for (const int kProperty : {vpiName, vpiFullName}) {
      const char* name = vpi_get_str(kProperty, assertion);
      if (name == nullptr || *name == '\0') continue;
      EXPECT_NE(vpi_handle_by_name(VpiText(name), top), assertion) << name;
      EXPECT_NE(vpi_handle_by_name(VpiText(name), nullptr), assertion) << name;
    }
  }
}

TEST_F(AssertionHandlesOfARun, EveryDeferredFormReportsItsImmediateKind) {
  Run("module top; logic a;\n"
      "  initial begin\n"
      "    m1: assume final (a);\n"
      "    c1: cover #0 (a);\n"
      "    a1: assert final (a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(KindOf("top", "m1"), vpiImmediateAssume);
  EXPECT_EQ(KindOf("top", "c1"), vpiImmediateCover);
  EXPECT_EQ(KindOf("top", "a1"), vpiImmediateAssert);
}

TEST_F(AssertionHandlesOfARun, AProceduralCoverPropertyIsACover) {
  Run("module top; logic clk, a;\n"
      "  always @(posedge clk) p1: cover property (a);\n"
      "endmodule\n");
  EXPECT_EQ(KindOf("top", "p1"), vpiCover);
}

TEST_F(AssertionHandlesOfARun, AnInstanceWalkReachesSequenceAndPropertyInsts) {
  Run("module top; logic clk, a;\n"
      "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
      "  property p; @(posedge clk) a; endproperty\n"
      "  c1: cover sequence (s);\n"
      "  a1: assert property (p);\n"
      "endmodule\n");
  const std::vector<int> kKinds = KindsOf(vpiAssertion, By("top"));
  EXPECT_EQ(std::ranges::count(kKinds, vpiSequenceInst), 1);
  EXPECT_EQ(std::ranges::count(kKinds, vpiPropertyInst), 1);
}

TEST_F(AssertionHandlesOfARun, ANameRelativeToAScopeFindsTheAssertion) {
  Run(kAssertionSites);
  vpiHandle as = Named(vpiAssertion, By("top.u1"), "as");
  vpiHandle ag = Named(vpiAssertion, By("top.g[1]"), "ag");
  ASSERT_NE(as, nullptr);
  ASSERT_NE(ag, nullptr);
  EXPECT_EQ(vpi_handle_by_name(VpiText("as"), By("top.u1")), as);
  EXPECT_EQ(vpi_handle_by_name(VpiText("u1.as"), By("top")), as);
  EXPECT_EQ(vpi_handle_by_name(VpiText("ag"), By("top.g[1]")), ag);
  EXPECT_EQ(vpi_handle_by_name(VpiText("g[1].ag"), By("top")), ag);
}

TEST_F(AssertionHandlesOfARun, AFullNameFindsAnAssertionWrittenAnywhere) {
  Run(kAssertionSites);
  for (const auto& [scope, name] :
       {std::pair<std::string, std::string>{"top", "pc"},
        {"top.g[1]", "ag"},
        {"top.b", "ai"},
        {"top.p", "ap"}}) {
    vpiHandle walked = Named(vpiAssertion, By(scope), name);
    ASSERT_NE(walked, nullptr) << name;
    std::string full_name = scope;
    full_name += ".";
    full_name += name;
    EXPECT_EQ(By(full_name), walked) << name;
  }
}

}  // namespace
}  // namespace delta
