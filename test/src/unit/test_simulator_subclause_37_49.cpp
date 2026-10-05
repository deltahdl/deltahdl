#include <gtest/gtest.h>

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

// §37.49 assertion: the VPI assertion object model. The assertion class groups
// the immediate/concurrent assertion kinds and sequence/property instances, is
// reachable from a null reference, traverses to its enclosing instance (reusing
// the §37.10 vpiInstance relation) and to its clocking block, and exposes a
// source span and a name. These tests observe the production helpers in vpi.cpp
// and the VpiContext methods that apply those rules.

// A: every object kind the assertion class groups is an assertion; unrelated
// object kinds (including a clocking block) are not.
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

// A edge: vpiAssertion names the class, not a concrete object kind, so the
// class selector itself is not classified as one of the grouped member kinds.
TEST(AssertionModel, ClassSelectorIsNotItselfAMemberKind) {
  EXPECT_FALSE(VpiIsAssertionType(vpiAssertion));
}

// A + circle: iterating the assertion class from a null reference returns every
// assertion-kind object in the design and skips non-assertions.
TEST(AssertionModel, IterateAssertionClassFromNullReturnsAllAssertions) {
  VpiContext ctx;
  VpiHandle a = ctx.CreateAssertion("a_req", vpiAssert);
  VpiHandle c = ctx.CreateAssertion("c_cov", vpiImmediateCover);
  ctx.CreateParameter("WIDTH", 8);  // not an assertion

  VpiHandle it = ctx.Iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], a);
  EXPECT_EQ(seen[1], c);
}

// D edge: with no assertions in the design, the class iteration reports nothing
// rather than handing back an empty iterator to scan.
TEST(AssertionModel, IterateAssertionClassWithNoAssertionsIsNull) {
  VpiContext ctx;
  ctx.CreateParameter("WIDTH", 8);  // a non-assertion object exists

  EXPECT_EQ(ctx.Iterate(vpiAssertion, nullptr), nullptr);
}

// A grouping: iterating the assertion class under a scope returns only the
// assertion-kind children of that scope, in order.
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

// C: an assertion traverses to its governing clocking block, and reports none
// when no clocking block is associated.
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

// C edge: a null handle yields no clocking block, and the relation matches by
// type, so an assertion whose children are all non-clocking reports none.
TEST(AssertionModel, ClockingBlockRelationRejectsNullAndOtherChildren) {
  EXPECT_EQ(VpiAssertionClockingBlock(nullptr), nullptr);

  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiAssertionClockingBlock(&assertion), nullptr);
}

// B (borrowed §37.10 vpiInstance): an assertion resolves to the nearest
// enclosing instance it is written in.
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

// B edge: an assertion that sits only inside non-instance scopes (e.g. a named
// block) with no enclosing instance resolves to no instance at all.
TEST(AssertionModel, AssertionWithoutEnclosingInstanceResolvesNone) {
  VpiObject block;
  block.type = vpiNamedBegin;  // a scope that is not an instance
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.parent = &block;

  EXPECT_EQ(VpiInstanceOf(&assertion), nullptr);
}

// E: the assertion exposes the integer span through vpi_get and its file/name
// through vpi_get_str.
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

// E edge: an assertion with no recorded span reports zero for each integer
// location component rather than an unset/garbage value.
TEST(AssertionModel, UnsetLocationSpanReportsZero) {
  VpiContext ctx;
  VpiObject assertion;
  assertion.type = vpiAssert;

  EXPECT_EQ(ctx.Get(vpiStartLine, &assertion), 0);
  EXPECT_EQ(ctx.Get(vpiColumn, &assertion), 0);
  EXPECT_EQ(ctx.Get(vpiEndLine, &assertion), 0);
  EXPECT_EQ(ctx.Get(vpiEndColumn, &assertion), 0);
}

// E edge: an assertion with no recorded file reports no file string rather than
// an empty one.
TEST(AssertionModel, MissingFileReportsNull) {
  VpiContext ctx;
  VpiObject assertion;
  assertion.type = vpiAssert;

  EXPECT_EQ(ctx.GetStr(vpiFile, &assertion), nullptr);
}

// E input form: the location and name property groups are drawn on the abstract
// assertion class, so they apply to every grouped member kind - not only the
// assert directive the other E tests use. An assertion registered as a property
// instance through the real construction path reports the name it was created
// with and the source span recorded on it just the same.
TEST(AssertionModel, LocationAndNameApplyToAnyAssertionMemberKind) {
  VpiContext ctx;
  VpiHandle p = ctx.CreateAssertion("p_handshake", vpiPropertyInst);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(VpiIsAssertionType(p->type));  // a property inst is an assertion
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

// The assertions of a run: those a design writes as module items, built from
// the elaborated design rather than by hand (#4955).
class AssertionsOfARun : public VpiDesignRun {};

// An instance reaches each assertion written as its item, of the kind it is,
// named by its label and reporting the line it starts on.
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

}  // namespace
}  // namespace delta
