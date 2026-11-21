#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(AssertionModel, AssertionTypeCoversTheGroupedKinds) {
  EXPECT_TRUE(VpiIsAssertionType(vpiAssert));
  EXPECT_TRUE(VpiIsAssertionType(vpiAssume));
  EXPECT_TRUE(VpiIsAssertionType(vpiCover));
  EXPECT_TRUE(VpiIsAssertionType(vpiRestrict));
  EXPECT_TRUE(VpiIsAssertionType(vpiImmediateAssert));
  EXPECT_TRUE(VpiIsAssertionType(vpiImmediateAssume));
  EXPECT_TRUE(VpiIsAssertionType(vpiImmediateCover));
  EXPECT_TRUE(VpiIsAssertionType(vpiSequenceInst));
  EXPECT_TRUE(VpiIsAssertionType(vpiPropertyInst));

  EXPECT_FALSE(VpiIsAssertionType(vpiModule));
  EXPECT_FALSE(VpiIsAssertionType(vpiNet));
  EXPECT_FALSE(VpiIsAssertionType(vpiClockingBlock));
}

TEST(AssertionModel, ClassSelectorIsNotItselfAMemberKind) {
  EXPECT_FALSE(VpiIsAssertionType(vpiAssertion));
}

TEST(AssertionModel, IterateAssertionClassFromNullReturnsAllAssertions) {
  VpiContext ctx;
  VpiHandle a = ctx.CreateAssertion("a_req", vpiAssert);
  VpiHandle c = ctx.CreateAssertion("c_cov", vpiImmediateCover);
  ctx.CreateParameter("WIDTH", 8);

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], a);
  EXPECT_EQ(seen[1], c);
}

TEST(AssertionModel, IterateAssertionClassWithNoAssertionsIsNull) {
  VpiContext ctx;
  ctx.CreateParameter("WIDTH", 8);

  EXPECT_EQ(ctx.Iterate(vpiAssertion, nullptr), nullptr);
}

TEST(AssertionModel, IterateAssertionClassUnderScopeFiltersChildren) {
  VpiContext ctx;
  VpiObject scope;
  VpiObject net_child;
  net_child.type = vpiNet;
  VpiObject assert_child;
  assert_child.type = vpiAssert;
  VpiObject seq_child;
  seq_child.type = vpiSequenceInst;
  scope.children = {&net_child, &assert_child, &seq_child};

  VpiHandle it = ctx.Iterate(vpiAssertion, &scope);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &assert_child);
  EXPECT_EQ(seen[1], &seq_child);
}

TEST(AssertionModel, ClockingBlockRelationFindsAssociatedBlock) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject clk;
  clk.type = vpiClockingBlock;
  assertion.children = {&clk};

  EXPECT_EQ(VpiAssertionClockingBlock(&assertion), &clk);

  VpiObject unclocked;
  unclocked.type = vpiAssert;
  EXPECT_EQ(VpiAssertionClockingBlock(&unclocked), nullptr);
}

TEST(AssertionModel, ClockingBlockRelationRejectsNullAndOtherChildren) {
  EXPECT_EQ(VpiAssertionClockingBlock(nullptr), nullptr);

  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiAssertionClockingBlock(&assertion), nullptr);
}

TEST(AssertionModel, AssertionResolvesEnclosingInstance) {
  VpiObject program;
  program.type = vpiProgram;
  VpiObject module;
  module.type = vpiModule;
  module.parent = &program;
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.parent = &module;

  EXPECT_EQ(VpiInstanceOf(&assertion), &module);
}

TEST(AssertionModel, AssertionWithoutEnclosingInstanceResolvesNone) {
  VpiObject block;
  block.type = vpiNamedBegin;
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.parent = &block;

  EXPECT_EQ(VpiInstanceOf(&assertion), nullptr);
}

TEST(AssertionModel, LocationAndNamePropertiesAreReported) {
  VpiContext ctx;
  std::string name = "handshake_p";
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.name = name;
  assertion.file = "top.sv";
  assertion.start_line = 12;
  assertion.column = 5;
  assertion.end_line = 14;
  assertion.end_column = 9;

  EXPECT_EQ(ctx.Get(vpiStartLine, &assertion), 12);
  EXPECT_EQ(ctx.Get(vpiColumn, &assertion), 5);
  EXPECT_EQ(ctx.Get(vpiEndLine, &assertion), 14);
  EXPECT_EQ(ctx.Get(vpiEndColumn, &assertion), 9);
  EXPECT_STREQ(ctx.GetStr(vpiFile, &assertion), "top.sv");
  EXPECT_STREQ(ctx.GetStr(vpiName, &assertion), "handshake_p");
}

TEST(AssertionModel, UnsetLocationSpanReportsZero) {
  VpiContext ctx;
  VpiObject assertion;
  assertion.type = vpiAssert;

  EXPECT_EQ(ctx.Get(vpiStartLine, &assertion), 0);
  EXPECT_EQ(ctx.Get(vpiColumn, &assertion), 0);
  EXPECT_EQ(ctx.Get(vpiEndLine, &assertion), 0);
  EXPECT_EQ(ctx.Get(vpiEndColumn, &assertion), 0);
}

TEST(AssertionModel, MissingFileReportsNull) {
  VpiContext ctx;
  VpiObject assertion;
  assertion.type = vpiAssert;

  EXPECT_EQ(ctx.GetStr(vpiFile, &assertion), nullptr);
}

TEST(AssertionModel, LocationAndNameApplyToAnyAssertionMemberKind) {
  VpiContext ctx;
  VpiHandle p = ctx.CreateAssertion("p_handshake", vpiPropertyInst);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(VpiIsAssertionType(p->type));
  p->file = "checks.sv";
  p->start_line = 40;
  p->column = 3;
  p->end_line = 42;
  p->end_column = 7;

  EXPECT_STREQ(ctx.GetStr(vpiName, p), "p_handshake");
  EXPECT_STREQ(ctx.GetStr(vpiFile, p), "checks.sv");
  EXPECT_EQ(ctx.Get(vpiStartLine, p), 40);
  EXPECT_EQ(ctx.Get(vpiColumn, p), 3);
  EXPECT_EQ(ctx.Get(vpiEndLine, p), 42);
  EXPECT_EQ(ctx.Get(vpiEndColumn, p), 7);
}

class AssertionsOfARun : public VpiDesignRun {};

TEST_F(AssertionsOfARun, AnInstanceReachesTheAssertionsItsItemsWrite) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "  m1: assume property (@(posedge clk) a);\n"
      "  c1: cover sequence (@(posedge clk) a ##1 a);\n"
      "  d1: assert #0 (a);\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle a1 = Named(vpiAssertion, top, "a1");
  vpiHandle m1 = Named(vpiAssertion, top, "m1");
  vpiHandle c1 = Named(vpiAssertion, top, "c1");
  vpiHandle d1 = Named(vpiAssertion, top, "d1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(m1, nullptr);
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(d1, nullptr);
  EXPECT_EQ(vpi_get(vpiType, a1), vpiAssert);
  EXPECT_EQ(vpi_get(vpiType, m1), vpiAssume);
  EXPECT_EQ(vpi_get(vpiType, c1), vpiCover);
  EXPECT_EQ(vpi_get(vpiType, d1), vpiImmediateAssert);
  EXPECT_EQ(vpi_get(vpiIsCoverSequence, c1), 1);
  EXPECT_STREQ(vpi_get_str(vpiFullName, a1), "top.a1");
  EXPECT_EQ(vpi_get(vpiStartLine, a1), 2);
  EXPECT_EQ(vpi_get(vpiStartLine, c1), 4);
}

TEST_F(AssertionsOfARun, AGenerateBlocksAssertionIsItsGenScopes) {
  Run("module top; logic clk, a;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    a1: assert property (@(posedge clk) a);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle g1 = By("top.g[1]");
  ASSERT_NE(g1, nullptr);
  vpiHandle a1 = Named(vpiAssertion, g1, "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, a1), "top.g[1].a1");
  EXPECT_EQ(FullNameOfChild(By("top"), "a1"), "");
}

TEST_F(AssertionsOfARun, AnAssertionReportsWhereItsTextEnds) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk)\n"
      "                       a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(vpi_get(vpiStartLine, a1), 2);
  EXPECT_EQ(vpi_get(vpiEndLine, a1), 3);
  EXPECT_EQ(vpi_get(vpiEndColumn, a1), 26);
}

TEST_F(AssertionsOfARun,
       AnInstanceReachesTheImmediateAssertionsOfItsProcedures) {
  Run("module top; logic a;\n"
      "  initial begin\n"
      "    a1: assert (a);\n"
      "    m1: assume (a);\n"
      "    c1: cover (a);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle a1 = Named(vpiAssertion, top, "a1");
  vpiHandle m1 = Named(vpiAssertion, top, "m1");
  vpiHandle c1 = Named(vpiAssertion, top, "c1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(m1, nullptr);
  ASSERT_NE(c1, nullptr);
  EXPECT_EQ(vpi_get(vpiType, a1), vpiImmediateAssert);
  EXPECT_EQ(vpi_get(vpiType, m1), vpiImmediateAssume);
  EXPECT_EQ(vpi_get(vpiType, c1), vpiImmediateCover);
  EXPECT_EQ(vpi_get(vpiStartLine, c1), 5);
  EXPECT_EQ(vpi_get(vpiEndLine, c1), 5);
  EXPECT_EQ(vpi_get(vpiEndColumn, c1), 18);
}

TEST_F(AssertionsOfARun,
       AnInstanceReachesTheConcurrentAssertionsOfItsProcedures) {
  Run("module top; logic clk, a;\n"
      "  always @(posedge clk) begin\n"
      "    p1: assert property (a);\n"
      "    q1: assume property (a);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle p1 = Named(vpiAssertion, top, "p1");
  vpiHandle q1 = Named(vpiAssertion, top, "q1");
  ASSERT_NE(p1, nullptr);
  ASSERT_NE(q1, nullptr);
  EXPECT_EQ(vpi_get(vpiType, p1), vpiAssert);
  EXPECT_EQ(vpi_get(vpiType, q1), vpiAssume);
  EXPECT_EQ(vpi_get(vpiStartLine, q1), 4);
}

TEST_F(AssertionsOfARun, AnAssertionReachesTheClockingBlockClockingIt) {
  Run("module top; logic clk, a; logic [1:0] v;\n"
      "  clocking other @(posedge clk); endclocking\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  a1: assert property (a);\n"
      "  a2: assert property (@(other) a);\n"
      "  a3: assert property (@(posedge clk) a);\n"
      "  a5: assert property (@(posedge clk or posedge a) a);\n"
      "  a6: assert property (@(clk) a);\n"
      "  a7: assert property (@(v[0]) a);\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    a4: assert property (a);\n"
      "  end\n"
      "  always @(posedge clk) begin\n"
      "    p1: assert property (a);\n"
      "    p2: assert property (@(other) a);\n"
      "  end\n"
      "  initial p3: assert property (a);\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  const auto kBlockOf = [](vpiHandle assertion) -> std::string {
    if (assertion == nullptr) return "no assertion";
    vpiHandle block = vpi_handle(vpiClockingBlock, assertion);
    return block == nullptr ? "" : vpi_get_str(vpiName, block);
  };
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "a1")), "cb");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "a2")), "other");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "a3")), "");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "a5")), "");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "a6")), "");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "a7")), "");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, By("top.g[0]"), "a4")), "cb");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "p1")), "");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "p2")), "other");
  EXPECT_EQ(kBlockOf(Named(vpiAssertion, top, "p3")), "cb");
}

std::string FullNameOf(vpiHandle obj) {
  const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiFullName, obj);
  return name == nullptr ? "" : name;
}

TEST_F(AssertionsOfARun, EveryConcurrentAndDeferredKindIsAnAssertion) {
  Run("module top; logic clk, a;\n"
      "  r1: restrict property (@(posedge clk) a);\n"
      "  c1: cover property (@(posedge clk) a);\n"
      "  c2: cover sequence (@(posedge clk) a);\n"
      "  initial begin\n"
      "    m1: assume #0 (a);\n"
      "    k1: cover final (a);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  const auto kTypeOf = [top](const char* name) {
    vpiHandle assertion = Named(vpiAssertion, top, name);
    return assertion == nullptr ? 0 : vpi_get(vpiType, assertion);
  };
  EXPECT_EQ(kTypeOf("r1"), vpiRestrict);
  EXPECT_EQ(kTypeOf("c1"), vpiCover);
  EXPECT_EQ(kTypeOf("c2"), vpiCover);
  EXPECT_EQ(kTypeOf("m1"), vpiImmediateAssume);
  EXPECT_EQ(kTypeOf("k1"), vpiImmediateCover);
  EXPECT_EQ(vpi_get(vpiIsCoverSequence, Named(vpiAssertion, top, "c1")), 0);
  EXPECT_EQ(vpi_get(vpiIsCoverSequence, Named(vpiAssertion, top, "c2")), 1);
}

constexpr const char* kAssertionsInEveryInstance =
    "interface bus(input logic clk); logic a;\n"
    "  ai: assert property (@(posedge clk) a);\n"
    "endinterface\n"
    "program prg(input logic clk); logic a;\n"
    "  ap: assert property (@(posedge clk) a);\n"
    "endprogram\n"
    "module top; logic clk, a; bus b(clk); prg p(clk);\n"
    "  am: assert property (@(posedge clk) a);\n"
    "  if (1) begin : g ag: assert property (@(posedge clk) a); end\n"
    "  initial begin ad: assert (a); end\n"
    "endmodule\n";

TEST_F(AssertionsOfARun, AnAssertionsInstanceIsTheInstanceAroundIt) {
  Run(kAssertionsInEveryInstance);
  const auto kInstanceOf = [](const char* scope, const char* name) {
    return FullNameOf(
        vpi_handle(vpiInstance, Named(vpiAssertion, By(scope), name)));
  };
  EXPECT_EQ(kInstanceOf("top", "am"), "top");
  EXPECT_EQ(kInstanceOf("top", "ad"), "top");
  EXPECT_EQ(kInstanceOf("top.b", "ai"), "top.b");
  EXPECT_EQ(kInstanceOf("top.p", "ap"), "top.p");
  EXPECT_EQ(kInstanceOf("top.g", "ag"), "top");
}

TEST_F(AssertionsOfARun, IteratingFromNullReachesEveryAssertionOfTheDesign) {
  Run(kAssertionsInEveryInstance);
  std::vector<std::string> names;
  for (vpiHandle assertion : ObjectsOf(vpiAssertion, nullptr)) {
    names.push_back(FullNameOf(assertion));
  }
  for (const char* name :
       {"top.am", "top.ad", "top.b.ai", "top.p.ap", "top.g.ag"}) {
    EXPECT_EQ(std::count(names.begin(), names.end(), name), 1) << name;
  }
}

TEST_F(AssertionsOfARun, AnAssertionReportsItsFileAndColumn) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a); a2: assert #0 (a);\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle a1 = Named(vpiAssertion, top, "a1");
  vpiHandle a2 = Named(vpiAssertion, top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  const char* file = vpi_get_str(vpiFile, a1);
  ASSERT_NE(file, nullptr);
  EXPECT_STREQ(file, "<test>");
  const int kFirst = vpi_get(vpiColumn, a1);
  const int kSecond = vpi_get(vpiColumn, a2);
  EXPECT_TRUE(kFirst == 3 || kFirst == 7) << kFirst;
  EXPECT_TRUE(kSecond == 43 || kSecond == 47) << kSecond;
  EXPECT_EQ(kSecond - kFirst, 40);
}

}  // namespace
}  // namespace delta
