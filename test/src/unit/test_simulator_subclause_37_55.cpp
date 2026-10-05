#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.55 immediate assertions: the VPI object model for an immediate assertion.
// The immediate-assertion class is realized by the immediate assert, immediate
// assume, and immediate cover directives. Each reaches its asserted expression
// through vpiExpr and its pass action statement through vpiStmt, and reports
// whether it is a deferred assertion (vpiIsDeferred) and whether it is a final
// assertion (vpiIsFinal). An immediate assert and an immediate assume also
// carry an else (fail) statement reached through vpiElseStmt; an immediate
// cover does not. These tests observe the production helpers in vpi.cpp and the
// VpiContext methods that apply those rules.

// The three immediate directive kinds are immediate assertions; the concurrent
// kinds (the broader §37.49 class) and unrelated kinds are not.
TEST(ImmediateAssertionModel, ImmediateAssertionTypeCoversTheThreeDirectives) {
  EXPECT_TRUE(VpiIsImmediateAssertionType(vpiImmediateAssert));
  EXPECT_TRUE(VpiIsImmediateAssertionType(vpiImmediateAssume));
  EXPECT_TRUE(VpiIsImmediateAssertionType(vpiImmediateCover));

  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiAssert));
  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiCover));
  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiModule));
}

// vpiIsDeferred and vpiIsFinal are Boolean properties of every immediate
// assertion kind; each reports the assertion's stored flag.
TEST(ImmediateAssertionModel, AssertReportsIsDeferredAndIsFinal) {
  VpiContext ctx;

  VpiObject deferred;
  deferred.type = vpiImmediateAssert;
  deferred.is_deferred = true;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &deferred), 1);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &deferred), 0);

  VpiObject final_assert;
  final_assert.type = vpiImmediateAssert;
  final_assert.is_final = true;
  EXPECT_EQ(ctx.Get(vpiIsFinal, &final_assert), 1);
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &final_assert), 0);
}

// The same two properties apply to the assume and cover kinds as well.
TEST(ImmediateAssertionModel, AssumeAndCoverReportIsDeferredAndIsFinal) {
  VpiContext ctx;

  VpiObject assume;
  assume.type = vpiImmediateAssume;
  assume.is_deferred = true;
  assume.is_final = true;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &assume), 1);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &assume), 1);

  // A cover carries the same properties: here the stored deferred flag is set
  // and the final flag is not, so each reports its own stored value (1 and 0)
  // rather than a shared one. This shows a true value flows through a cover,
  // not only the default.
  VpiObject cover;
  cover.type = vpiImmediateCover;
  cover.is_deferred = true;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &cover), 1);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &cover), 0);
}

// The deferred/final properties are drawn only on the immediate-assertion
// kinds, so querying them on any other object kind is not valid and yields
// vpiUndefined.
TEST(ImmediateAssertionModel, IsDeferredAndIsFinalAreUndefinedElsewhere) {
  VpiContext ctx;

  VpiObject mod;
  mod.type = vpiModule;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &mod), vpiUndefined);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &mod), vpiUndefined);

  // A concurrent assertion is not an immediate assertion, so it has no
  // deferred/final property either.
  VpiObject concurrent;
  concurrent.type = vpiAssert;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &concurrent), vpiUndefined);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &concurrent), vpiUndefined);
}

// Every immediate-assertion kind reaches its asserted expression through
// vpiExpr, modeled as its first expression child, and its pass action statement
// through vpiStmt. The diagram draws both edges from each of the assert,
// assume, and cover boxes, so the traversals are observed on all three kinds.
TEST(ImmediateAssertionModel, EachKindReachesExpressionAndPassStatement) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  for (int kind : {vpiImmediateAssert, vpiImmediateAssume, vpiImmediateCover}) {
    VpiObject assertion;
    assertion.type = kind;
    VpiObject expr;
    expr.type = vpiOperation;  // an expr-class kind
    VpiObject pass;
    // §37.55 draws the edge to a `stmt`, and a statement's own type is a
    // statement kind rather than the vpiStmt relation tag.
    pass.type = vpiBegin;
    assertion.children = {&expr, &pass};

    // The figure's edges through the public routine, which is where an
    // application reads them.
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&assertion))), &expr)
        << "kind=" << kind;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&assertion))), &pass)
        << "kind=" << kind;
  }

  EXPECT_EQ(VpiImmediateAssertionExpr(nullptr), nullptr);
  EXPECT_EQ(VpiImmediateAssertionStmt(nullptr), nullptr);
  SetGlobalVpiContext(nullptr);
}

// vpiElseStmt is routed from the assert and assume boxes but not from cover, so
// only an immediate assert or assume carries an else (fail) statement.
TEST(ImmediateAssertionModel, ElseStatementPresenceByKind) {
  EXPECT_TRUE(VpiImmediateAssertionHasElseStmt(vpiImmediateAssert));
  EXPECT_TRUE(VpiImmediateAssertionHasElseStmt(vpiImmediateAssume));
  EXPECT_FALSE(VpiImmediateAssertionHasElseStmt(vpiImmediateCover));
}

// An immediate assert traverses to its else statement through vpiElseStmt; an
// immediate cover, built with only a pass statement, reaches none.
TEST(ImmediateAssertionModel, AssertReachesElseStatementCoverDoesNot) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  // The two action statements in the order they were written: the pass action
  // first, the else action after it. Each carries its own statement kind, not
  // the relation tag naming the edge that reaches it.
  VpiObject assertion;
  assertion.type = vpiImmediateAssert;
  VpiObject pass;
  pass.type = vpiBegin;
  VpiObject els;
  els.type = vpiAssignment;
  assertion.children = {&pass, &els};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&assertion))), &pass);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&assertion))),
            &els);

  // The figure draws no vpiElseStmt edge from the cover box, so a cover reaches
  // no else action however many statements it was written with.
  VpiObject cover;
  cover.type = vpiImmediateCover;
  VpiObject cover_pass;
  cover_pass.type = vpiBegin;
  VpiObject cover_second;
  cover_second.type = vpiAssignment;
  cover.children = {&cover_pass, &cover_second};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&cover))), &cover_pass);
  EXPECT_EQ(vpi_handle(vpiElseStmt, VpiHandleOf(&cover)), nullptr);

  EXPECT_EQ(VpiImmediateAssertionElseStmt(nullptr), nullptr);
  SetGlobalVpiContext(nullptr);
}

// The traversals each match by kind, so an immediate assertion whose only child
// is an unrelated object reaches neither an expression nor a statement.
TEST(ImmediateAssertionModel, TraversalsSkipUnrelatedChildren) {
  VpiObject assertion;
  assertion.type = vpiImmediateAssume;
  VpiObject module_child;
  module_child.type = vpiModule;
  assertion.children = {&module_child};
  EXPECT_EQ(VpiImmediateAssertionExpr(&assertion), nullptr);
  EXPECT_EQ(VpiImmediateAssertionStmt(&assertion), nullptr);
  EXPECT_EQ(VpiImmediateAssertionElseStmt(&assertion), nullptr);
}

// The immediate assertions of a run, built from the elaborated design rather
// than by hand.
class ImmediateAssertionsOfARun : public VpiDesignRun {
 protected:
  // The name of what `assertion` reaches through `relation`, empty for none.
  static std::string NameReached(int relation, vpiHandle assertion) {
    vpiHandle reached = vpi_handle(relation, assertion);
    if (reached == nullptr) return "";
    const char* name = vpi_get_str(vpiName, reached);
    return name == nullptr ? "" : name;
  }
};

// An assertion statement reaches the expression it asserts and its pass and
// fail actions, and reports that it is not deferred; a cover has no fail
// action (#5075).
TEST_F(ImmediateAssertionsOfARun, AnAssertionStatementReachesItsParts) {
  Run("module top; logic a, b;\n"
      "  initial begin\n"
      "    a1: assert (a) $display(\"p\"); else $write(\"f\");\n"
      "    c1: cover (b) $display(\"c\");\n"
      "  end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle a1 = Named(vpiAssertion, top, "a1");
  vpiHandle c1 = Named(vpiAssertion, top, "c1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(c1, nullptr);
  EXPECT_EQ(NameReached(vpiExpr, a1), "a");
  EXPECT_EQ(NameReached(vpiStmt, a1), "$display");
  EXPECT_EQ(NameReached(vpiElseStmt, a1), "$write");
  EXPECT_EQ(vpi_get(vpiIsDeferred, a1), 0);
  EXPECT_EQ(NameReached(vpiExpr, c1), "b");
  EXPECT_EQ(NameReached(vpiStmt, c1), "$display");
  EXPECT_EQ(vpi_handle(vpiElseStmt, c1), nullptr);
}

// A deferred assertion written as a module item reaches its expression and
// actions, and reports whether it is deferred and whether final (#5078).
TEST_F(ImmediateAssertionsOfARun, ADeferredAssertionItemReachesItsParts) {
  Run("module top; logic a, b;\n"
      "  d1: assert final (a) $display(\"p\"); else $write(\"f\");\n"
      "  d2: assert #0 (b);\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle d1 = Named(vpiAssertion, top, "d1");
  vpiHandle d2 = Named(vpiAssertion, top, "d2");
  ASSERT_NE(d1, nullptr);
  ASSERT_NE(d2, nullptr);
  EXPECT_EQ(NameReached(vpiExpr, d1), "a");
  EXPECT_EQ(NameReached(vpiStmt, d1), "$display");
  EXPECT_EQ(NameReached(vpiElseStmt, d1), "$write");
  EXPECT_EQ(vpi_get(vpiIsDeferred, d1), 1);
  EXPECT_EQ(vpi_get(vpiIsFinal, d1), 1);
  EXPECT_EQ(NameReached(vpiExpr, d2), "b");
  EXPECT_EQ(vpi_get(vpiIsDeferred, d2), 1);
  EXPECT_EQ(vpi_get(vpiIsFinal, d2), 0);
}

// An assertion written with a fail action and no pass action reaches that
// action through vpiElseStmt and no statement through vpiStmt (#5083).
TEST_F(ImmediateAssertionsOfARun, AFailActionAloneIsTheElseStatement) {
  Run("module top; logic a;\n"
      "  initial begin\n"
      "    a1: assert (a) else $write(\"f\");\n"
      "  end\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, a1), nullptr);
  EXPECT_EQ(NameReached(vpiElseStmt, a1), "$write");
}

}  // namespace
}  // namespace delta
