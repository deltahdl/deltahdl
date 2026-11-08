#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(RecursivePropertyDetection, SelfInstantiationIsRecursiveSingleCallIsNot) {
  PropertyRegistry reg;
  ModuleItem rec;
  rec.kind = ModuleItemKind::kPropertyDecl;
  rec.name = "prop_always";
  rec.prop_instance_refs = {"prop_always"};
  ModuleItem caller;
  caller.kind = ModuleItemKind::kPropertyDecl;
  caller.name = "p1";
  caller.prop_instance_refs = {"prop_always"};
  reg.Register(&rec);
  reg.Register(&caller);

  EXPECT_TRUE(reg.IsRecursiveProperty(&rec));
  EXPECT_FALSE(reg.IsRecursiveProperty(&caller));
  EXPECT_TRUE(reg.ReachesRecursiveProperty(&caller));
  EXPECT_TRUE(reg.ReachesRecursiveProperty(&rec));
}

TEST(RecursivePropertyDetection, MutuallyRecursivePropertiesAreRecursive) {
  PropertyRegistry reg;
  ModuleItem a;
  a.kind = ModuleItemKind::kPropertyDecl;
  a.name = "check_phase1";
  a.prop_instance_refs = {"check_phase2"};
  ModuleItem b;
  b.kind = ModuleItemKind::kPropertyDecl;
  b.name = "check_phase2";
  b.prop_instance_refs = {"check_phase1"};
  reg.Register(&a);
  reg.Register(&b);

  EXPECT_TRUE(reg.IsRecursiveProperty(&a));
  EXPECT_TRUE(reg.IsRecursiveProperty(&b));
}

TEST(RecursivePropertyRestrictions, WellFormedRecursivePropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property prop_always(p);\n"
      "    p and (1'b1 |=> prop_always(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions, NotAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property prop_always(p);\n"
      "    p and (1'b1 |=> prop_always(p));\n"
      "  endproperty\n"
      "  property illegal_recursion_1(p);\n"
      "    not prop_always(not p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "\"prop_always\", which reaches a recursive property (Restriction 1)", 5,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictions, NotAppliedToSelfInstanceRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property illegal_recursion_2(p);\n"
      "    p and (1'b1 |=> not illegal_recursion_2(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "\"illegal_recursion_2\", which reaches a recursive "
                    "property (Restriction 1)",
                    2, "16.12.17"));
}

TEST(RecursivePropertyRestrictions,
     StrongOperatorAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    s_eventually rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "\"rec\", which reaches a recursive property (Restriction 1)", 5,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictions,
     SNexttimeAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    s_nexttime rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "\"rec\", which reaches a recursive property (Restriction 1)", 5,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictions, SAlwaysAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    s_always [1:2] rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "\"rec\", which reaches a recursive property (Restriction 1)", 5,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictions,
     BracketedStrongOperatorsAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad_next(p);\n"
      "    s_nexttime [2] rec(p);\n"
      "  endproperty\n"
      "  property bad_eventually(p);\n"
      "    s_eventually [1:2] rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 8u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "\"rec\", which reaches a recursive property (Restriction 1)", line,
        "16.12.17"));
  }
}

TEST(RecursivePropertyRestrictions, SUntilAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    p s_until rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "\"rec\", which reaches a recursive property (Restriction 1)", 5,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictions,
     SUntilWithAppliedToRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    p s_until_with rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "\"rec\", which reaches a recursive property (Restriction 1)", 5,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictions, NotAppliedToNonRecursivePropertyAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property leaf(p);\n"
      "    p |-> 1'b1;\n"
      "  endproperty\n"
      "  property user(p);\n"
      "    not leaf(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions, NotThroughParenthesesOnRecursiveRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    not (rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "\"rec\", which reaches a recursive property (Restriction 1)", 5,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictions, DisableIffInRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic b);\n"
      "  property illegal_recursion_3(p);\n"
      "    disable iff (b)\n"
      "    p and (1'b1 |=> illegal_recursion_3(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive property \"illegal_recursion_3\" may "
                            "not use disable iff (Restriction 2)",
                            2, "16.12.17"));
}

TEST(RecursivePropertyRestrictions, DisableIffInNonRecursivePropertyAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic b);\n"
      "  property prop_always(p);\n"
      "    p and (1'b1 |=> prop_always(p));\n"
      "  endproperty\n"
      "  property legal_3(p);\n"
      "    disable iff (b) prop_always(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions, SelfInstanceWithoutTimeAdvanceRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property illegal_recursion_4(p);\n"
      "    p and (1'b1 |-> illegal_recursion_4(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "recursive property \"illegal_recursion_4\" lies on a "
                    "recursion cycle with no positive advance in time "
                    "(Restriction 3)",
                    2, "16.12.17"));
}

TEST(RecursivePropertyRestrictions, SelfInstanceAfterCycleDelayAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p ##1 rec(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions,
     MutuallyRecursiveInstancesWithoutTimeAdvanceRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property a(p);\n"
      "    p and b(p);\n"
      "  endproperty\n"
      "  property b(p);\n"
      "    p and a(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive property \"a\" lies on a recursion "
                            "cycle with no positive advance in time "
                            "(Restriction 3)",
                            2, "16.12.17"));
}

TEST(RecursivePropertyRestrictions,
     MutuallyRecursiveInstancesWithTimeAdvanceAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property a(p);\n"
      "    p and (1'b1 |=> b(p));\n"
      "  endproperty\n"
      "  property b(p);\n"
      "    p and a(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions, RecursiveArgsBoundToLocalFormalsAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property fibonacci1 (local input int a, b, n, int fib_sig);\n"
      "    (n > 0) |->\n"
      "    ((fib_sig == a) and (1'b1 |=> fibonacci1(b, a + b, n - 1, "
      "fib_sig)));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions,
     RecursiveArgsNotBoundToLocalFormalsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property fibonacci2 (int a, b, n, fib_sig);\n"
      "    (n > 0) |->\n"
      "    ((fib_sig == a) and (1'b1 |=> fibonacci2(b, a + b, n - 1, "
      "fib_sig)));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "recursive instance of \"fibonacci2\" passes an actual argument that "
      "contains a formal of \"fibonacci2\" yet is neither a formal itself nor "
      "bound to a local variable formal (Restriction 4)",
      2, "16.12.17"));
}

TEST(RecursivePropertyRestrictions, RecursiveArgWithNoEnclosingFormalAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property rec(p, n);\n"
      "    p and (1'b1 |=> rec(p, 5));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions,
     RecursiveArgParameterWithNoEnclosingFormalAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int K = 5;\n"
      "  property rec(p, n);\n"
      "    p and (1'b1 |=> rec(p, K));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions, AbortOperatorsAllowedInRecursiveProperty) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p3(p, bit b, abort);\n"
      "    (p and (1'b1 |=> p4(p, b, abort)));\n"
      "  endproperty\n"
      "  property p4(p, bit b, abort);\n"
      "    accept_on(b) reject_on(abort) p3(p, b, abort);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictions, NotInAnAssertionStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  bit clk, a;\n"
      "  property prop_always(p);\n"
      "    p and (1'b1 |=> prop_always(p));\n"
      "  endproperty\n"
      "  a1: assert property (@(posedge clk) not prop_always(a));\n"
      "  a2: assert property (@(posedge clk) s_eventually prop_always(a));\n"
      "  a3: assert property (@(posedge clk) prop_always(a));\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "\"prop_always\", which reaches a recursive property (Restriction 1)";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.12.17"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.12.17"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 8, "16.12.17"));
}

}  // namespace
