#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
  for (int kind : {vpiImmediateAssert, vpiImmediateAssume, vpiImmediateCover}) {
    VpiObject assertion;
    assertion.type = kind;
    VpiObject expr;
    expr.type = vpiOperation;  // an expr-class kind
    VpiObject pass;
    pass.type = vpiStmt;
    assertion.children = {&expr, &pass};

    EXPECT_EQ(VpiImmediateAssertionExpr(&assertion), &expr) << "kind=" << kind;
    EXPECT_EQ(VpiImmediateAssertionStmt(&assertion), &pass) << "kind=" << kind;
  }

  EXPECT_EQ(VpiImmediateAssertionExpr(nullptr), nullptr);
  EXPECT_EQ(VpiImmediateAssertionStmt(nullptr), nullptr);
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
  VpiObject assertion;
  assertion.type = vpiImmediateAssert;
  VpiObject pass;
  pass.type = vpiStmt;
  VpiObject els;
  els.type = vpiElseStmt;
  assertion.children = {&pass, &els};
  EXPECT_EQ(VpiImmediateAssertionElseStmt(&assertion), &els);

  VpiObject cover;
  cover.type = vpiImmediateCover;
  VpiObject cover_pass;
  cover_pass.type = vpiStmt;
  cover.children = {&cover_pass};
  EXPECT_EQ(VpiImmediateAssertionStmt(&cover), &cover_pass);
  EXPECT_EQ(VpiImmediateAssertionElseStmt(&cover), nullptr);

  EXPECT_EQ(VpiImmediateAssertionElseStmt(nullptr), nullptr);
}

// The traversals each match by kind, so an immediate assertion whose only child
// is an unrelated object reaches neither an expression nor a statement.
TEST(ImmediateAssertionModel, TraversalsSkipUnrelatedChildren) {
  VpiObject assertion;
  assertion.type = vpiImmediateAssume;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiImmediateAssertionExpr(&assertion), nullptr);
  EXPECT_EQ(VpiImmediateAssertionStmt(&assertion), nullptr);
  EXPECT_EQ(VpiImmediateAssertionElseStmt(&assertion), nullptr);
}

}  // namespace
}  // namespace delta
