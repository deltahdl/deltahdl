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

TEST(ImmediateAssertionModel, ImmediateAssertionTypeCoversTheThreeDirectives) {
  EXPECT_TRUE(VpiIsImmediateAssertionType(vpiImmediateAssert));
  EXPECT_TRUE(VpiIsImmediateAssertionType(vpiImmediateAssume));
  EXPECT_TRUE(VpiIsImmediateAssertionType(vpiImmediateCover));

  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiAssert));
  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiCover));
  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsImmediateAssertionType(vpiModule));
}

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

TEST(ImmediateAssertionModel, AssumeAndCoverReportIsDeferredAndIsFinal) {
  VpiContext ctx;

  VpiObject assume;
  assume.type = vpiImmediateAssume;
  assume.is_deferred = true;
  assume.is_final = true;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &assume), 1);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &assume), 1);

  VpiObject cover;
  cover.type = vpiImmediateCover;
  cover.is_deferred = true;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &cover), 1);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &cover), 0);
}

TEST(ImmediateAssertionModel, IsDeferredAndIsFinalAreUndefinedElsewhere) {
  VpiContext ctx;

  VpiObject mod;
  mod.type = vpiModule;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &mod), vpiUndefined);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &mod), vpiUndefined);

  VpiObject concurrent;
  concurrent.type = vpiAssert;
  EXPECT_EQ(ctx.Get(vpiIsDeferred, &concurrent), vpiUndefined);
  EXPECT_EQ(ctx.Get(vpiIsFinal, &concurrent), vpiUndefined);
}

TEST(ImmediateAssertionModel, EachKindReachesExpressionAndPassStatement) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  for (int kind : {vpiImmediateAssert, vpiImmediateAssume, vpiImmediateCover}) {
    VpiObject assertion;
    assertion.type = kind;
    VpiObject expr;
    expr.type = vpiOperation;
    VpiObject pass;
    pass.type = vpiBegin;
    assertion.children = {&expr, &pass};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&assertion))), &expr)
        << "kind=" << kind;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&assertion))), &pass)
        << "kind=" << kind;
  }

  EXPECT_EQ(VpiImmediateAssertionExpr(nullptr), nullptr);
  EXPECT_EQ(VpiImmediateAssertionStmt(nullptr), nullptr);
  SetGlobalVpiContext(nullptr);
}

TEST(ImmediateAssertionModel, ElseStatementPresenceByKind) {
  EXPECT_TRUE(VpiImmediateAssertionHasElseStmt(vpiImmediateAssert));
  EXPECT_TRUE(VpiImmediateAssertionHasElseStmt(vpiImmediateAssume));
  EXPECT_FALSE(VpiImmediateAssertionHasElseStmt(vpiImmediateCover));
}

TEST(ImmediateAssertionModel, AssertReachesElseStatementCoverDoesNot) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

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

class ImmediateAssertionsOfARun : public VpiDesignRun {
 protected:
  static std::string NameReached(int relation, vpiHandle assertion) {
    vpiHandle reached = vpi_handle(relation, assertion);
    if (reached == nullptr) return "";
    const char* name = vpi_get_str(vpiName, reached);
    return name == nullptr ? "" : name;
  }
};

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
  EXPECT_EQ(ActionReached(vpiStmt, a1), "$display");
  EXPECT_EQ(ActionReached(vpiElseStmt, a1), "$write");
  EXPECT_EQ(vpi_get(vpiIsDeferred, a1), 0);
  EXPECT_EQ(NameReached(vpiExpr, c1), "b");
  EXPECT_EQ(ActionReached(vpiStmt, c1), "$display");
  EXPECT_EQ(vpi_handle(vpiElseStmt, c1), nullptr);
}

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
  EXPECT_EQ(ActionReached(vpiStmt, d1), "$display");
  EXPECT_EQ(ActionReached(vpiElseStmt, d1), "$write");
  EXPECT_EQ(vpi_get(vpiIsDeferred, d1), 1);
  EXPECT_EQ(vpi_get(vpiIsFinal, d1), 1);
  EXPECT_EQ(NameReached(vpiExpr, d2), "b");
  EXPECT_EQ(vpi_get(vpiIsDeferred, d2), 1);
  EXPECT_EQ(vpi_get(vpiIsFinal, d2), 0);
}

TEST_F(ImmediateAssertionsOfARun, AFailActionAloneIsTheElseStatement) {
  Run("module top; logic a;\n"
      "  initial begin\n"
      "    a1: assert (a) else $write(\"f\");\n"
      "  end\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, a1), nullptr);
  EXPECT_EQ(ActionReached(vpiElseStmt, a1), "$write");
}

}  // namespace
}  // namespace delta
