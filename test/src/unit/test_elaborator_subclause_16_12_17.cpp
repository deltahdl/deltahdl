#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

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

constexpr const char* kRecursiveDeclarationPlaces[] = {
    "module",  "package",  "interface", "program",
    "checker", "generate", "clocking",  "unit"};

std::string RecursionIn(const std::string& place, const std::string& decls) {
  const std::string kSignals = "  bit clk, b; ";
  if (place == "unit")
    return "\n" + kSignals + decls + "\nmodule top; endmodule\n";
  if (place == "package") {
    return "package pk;\n" + kSignals + decls +
           "\nendpackage\nmodule top; endmodule\n";
  }
  if (place == "interface" || place == "program" || place == "checker") {
    return place + " m;\n" + kSignals + decls + "\nend" + place +
           "\nmodule top; m u(); endmodule\n";
  }
  std::string line = decls;
  if (place == "generate") line = "if (1) begin : g " + decls + " end";
  if (place == "clocking") {
    line = "clocking cb @(posedge clk); " + decls + " endclocking";
  }
  return "module top;\n" + kSignals + line + "\nendmodule\n";
}

struct ForbiddenRecursion {
  const char* decls;
  const char* report;
};

constexpr const char* kRec =
    "property rec(p); p and (1'b1 |=> rec(p)); endproperty ";

const ForbiddenRecursion kNegatedRecursions[] = {
    {"property bad(p); not rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); not (rec(p)); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); s_nexttime rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); s_nexttime [2] rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); s_eventually rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); s_eventually [1:2] rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); s_always [1:2] rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); p s_until rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property bad(p); p s_until_with rec(p); endproperty",
     "\"rec\", which reaches a recursive property (Restriction 1)"},
    {"property mid(p); rec(p); endproperty property bad(p); not mid(p); "
     "endproperty",
     "\"mid\", which reaches a recursive property (Restriction 1)"},
    {"property r1(p); p and (1'b1 |=> not r1(p)); endproperty",
     "\"r1\", which reaches a recursive property (Restriction 1)"}};

const ForbiddenRecursion kDisableIffRecursions[] = {
    {"property r1(p); disable iff (b) p and (1'b1 |=> r1(p)); endproperty",
     "recursive property \"r1\" may not use disable iff (Restriction 2)"},
    {"property r1(p); disable iff (b) p and (1'b1 |=> r2(p)); endproperty "
     "property r2(p); p and r1(p); endproperty",
     "recursive property \"r1\" may not use disable iff (Restriction 2)"}};

const ForbiddenRecursion kStallingRecursions[] = {
    {"property r1(p); p and (1'b1 |-> r1(p)); endproperty",
     "recursive property \"r1\" lies on a recursion cycle with no positive "
     "advance in time (Restriction 3)"},
    {"property r1(p); p #-# r1(p); endproperty",
     "recursive property \"r1\" lies on a recursion cycle with no positive "
     "advance in time (Restriction 3)"},
    {"property r1(p); if (b) r1(p); endproperty",
     "recursive property \"r1\" lies on a recursion cycle with no positive "
     "advance in time (Restriction 3)"},
    {"property r1(p); p and r2(p); endproperty property r2(p); p and r1(p); "
     "endproperty",
     "recursive property \"r1\" lies on a recursion cycle with no positive "
     "advance in time (Restriction 3)"}};

const ForbiddenRecursion kArgumentRecursions[] = {
    {"property r1(int a, n); (n > 0) |-> ((a > 0) and (1'b1 |=> r1(a + 1, n - "
     "1))); endproperty",
     "recursive instance of \"r1\" passes an actual argument that contains a "
     "formal of \"r1\" yet is neither a formal itself nor bound to a local "
     "variable formal (Restriction 4)"},
    {"property r1(p, int n); p and (1'b1 |=> r2(p, n + 1)); endproperty "
     "property r2(p, int n); p and (1'b1 |=> r1(p, n)); endproperty",
     "recursive instance of \"r2\" passes an actual argument that contains a "
     "formal of \"r1\" yet is neither a formal itself nor bound to a local "
     "variable formal (Restriction 4)"}};

constexpr const char* kAllowedRecursions[] = {
    "property ok(p); rec(p); endproperty",
    "property ok(p); nexttime rec(p); endproperty",
    "property ok(p); nexttime [2] rec(p); endproperty",
    "property ok(p); eventually [1:2] rec(p); endproperty",
    "property ok(p); always rec(p); endproperty",
    "property ok(p); always [1:2] rec(p); endproperty",
    "property ok(p); p until rec(p); endproperty",
    "property ok(p); p until_with rec(p); endproperty",
    "property leaf(p); p |-> 1'b1; endproperty property ok(p); not leaf(p); "
    "endproperty",
    "property ok(p); disable iff (b) rec(p); endproperty",
    "property r1(p); p and nexttime r1(p); endproperty",
    "property r1(p); p ##1 r1(p); endproperty",
    "property r1(p); p and (1'b1 |=> r2(p)); endproperty property r2(p); p "
    "and r1(p); endproperty",
    "property r1(local input int a, n); (n > 0) |-> ((a > 0) and (1'b1 |=> "
    "r1(a + 1, n - 1))); endproperty",
    "property r1(p, int n); p and (1'b1 |=> r2(p, n + 1)); endproperty "
    "property r2(p, local input int n); p and (1'b1 |=> r1(p, n)); "
    "endproperty",
    "property r1(p, int n); p and (1'b1 |=> r1(p, 5)); endproperty",
    "property r1(p, int n); p and (1'b1 |=> r1(p, n)); endproperty",
    "property r1(p, bit c, abort); accept_on(c) reject_on(abort) p and (1'b1 "
    "|=> r1(p, c, abort)); endproperty",
    "property r1(p, bit c, abort); sync_accept_on(c) sync_reject_on(abort) p "
    "and (1'b1 |=> r1(p, c, abort)); endproperty"};

template <size_t N>
void ExpectRecursionsReported(const char* place,
                              const ForbiddenRecursion (&recursions)[N]) {
  for (const ForbiddenRecursion& recursion : recursions) {
    SCOPED_TRACE(std::string(place) + " " + recursion.decls);
    ElabFixture f;
    ElaborateSrc(RecursionIn(place, std::string(kRec) + recursion.decls), f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), recursion.report, 2, "16.12.17"));
  }
}

constexpr const char* kCheckedRecursionPlaces[] = {
    "module", "interface", "program", "checker", "generate"};

constexpr const char* kUncheckedRecursionPlaces[] = {"package", "clocking",
                                                     "unit"};

TEST(RecursivePropertyPlaces, AForbiddenRecursionIsReportedInEachPlace) {
  for (const char* place : kCheckedRecursionPlaces) {
    ExpectRecursionsReported(place, kNegatedRecursions);
    ExpectRecursionsReported(place, kDisableIffRecursions);
    ExpectRecursionsReported(place, kStallingRecursions);
    ExpectRecursionsReported(place, kArgumentRecursions);
  }
}

TEST(RecursivePropertyPlaces,
     DISABLED_ANegatedOrStrongRecursionIsReportedInAPackageClockingOrUnit) {
  for (const char* place : kUncheckedRecursionPlaces) {
    ExpectRecursionsReported(place, kNegatedRecursions);
  }
}

TEST(RecursivePropertyPlaces,
     DISABLED_DisableIffInARecursionIsReportedInAPackageClockingOrUnit) {
  for (const char* place : kUncheckedRecursionPlaces) {
    ExpectRecursionsReported(place, kDisableIffRecursions);
  }
}

TEST(RecursivePropertyPlaces,
     DISABLED_ARecursionWithoutTimeAdvanceIsReportedInAPackageClockingOrUnit) {
  for (const char* place : kUncheckedRecursionPlaces) {
    ExpectRecursionsReported(place, kStallingRecursions);
  }
}

TEST(RecursivePropertyPlaces,
     DISABLED_AnActualOverAFormalIsReportedInAPackageClockingOrUnit) {
  for (const char* place : kUncheckedRecursionPlaces) {
    ExpectRecursionsReported(place, kArgumentRecursions);
  }
}

TEST(RecursivePropertyPlaces, AnAllowedRecursionIsAcceptedInEachPlace) {
  for (const char* place : kRecursiveDeclarationPlaces) {
    for (const char* decls : kAllowedRecursions) {
      SCOPED_TRACE(std::string(place) + " " + decls);
      ElabFixture f;
      ElaborateSrc(RecursionIn(place, std::string(kRec) + decls), f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(RecursivePropertyPlaces,
     DISABLED_AFollowedByWithoutOverlapAdvancesTimeInEachPlace) {
  for (const char* place : kRecursiveDeclarationPlaces) {
    SCOPED_TRACE(place);
    ElabFixture f;
    ElaborateSrc(RecursionIn(place, "property r1(p); p #=# r1(p); endproperty"),
                 f);
    EXPECT_FALSE(f.has_errors);
  }
}

constexpr const char* kRecursiveStatementPlaces[] = {
    "module", "procedural", "generate", "interface", "program", "checker"};

std::string RecursiveAssertionIn(const std::string& place,
                                 const std::string& spec) {
  const std::string kDecls =
      "  bit clk, a; property rec(p); p and (1'b1 |=> rec(p)); endproperty "
      "property mid(p); rec(p); endproperty\n";
  std::string line = "  a1: assert property (@(posedge clk) " + spec + ");";
  if (place == "procedural") {
    line = "  always @(posedge clk) a1: assert property (" + spec + ");";
  }
  if (place == "generate") line = "  if (1) begin : g" + line + " end";
  if (place == "interface" || place == "program" || place == "checker") {
    return place + " m;\n" + kDecls + line + "\nend" + place +
           "\nmodule top; m u(); endmodule\n";
  }
  return "module top;\n" + kDecls + line + "\nendmodule\n";
}

constexpr const char* kStrongRecursionSpecs[] = {
    "s_nexttime rec(a)", "s_eventually rec(a)", "s_always [1:2] rec(a)",
    "a s_until rec(a)", "a s_until_with rec(a)"};

constexpr const char* kNegatedRecursionSpecs[] = {"not rec(a)", "not mid(a)"};

void ExpectRecursionInAssertionReported(const char* place, const char* spec) {
  SCOPED_TRACE(std::string(place) + " " + spec);
  ElabFixture f;
  ElaborateSrc(RecursiveAssertionIn(place, spec), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "which reaches a recursive property "
                            "(Restriction 1)",
                            3, "16.12.17"));
}

TEST(RecursivePropertyPlaces,
     ANegatedOrStrongRecursionInAnAssertionIsReportedInEachPlace) {
  for (const char* place : {"module", "interface", "program", "checker"}) {
    for (const char* spec : kNegatedRecursionSpecs) {
      ExpectRecursionInAssertionReported(place, spec);
    }
    for (const char* spec : kStrongRecursionSpecs) {
      ExpectRecursionInAssertionReported(place, spec);
    }
  }
  for (const char* spec : kStrongRecursionSpecs) {
    ExpectRecursionInAssertionReported("procedural", spec);
  }
}

TEST(RecursivePropertyPlaces,
     DISABLED_ANegatedRecursionInAProceduralOrGenerateAssertionIsReported) {
  for (const char* spec : kNegatedRecursionSpecs) {
    ExpectRecursionInAssertionReported("procedural", spec);
    ExpectRecursionInAssertionReported("generate", spec);
  }
  for (const char* spec : kStrongRecursionSpecs) {
    ExpectRecursionInAssertionReported("generate", spec);
  }
}

TEST(RecursivePropertyPlaces,
     AWeakOrPlainRecursionInAnAssertionIsAcceptedInEachPlace) {
  for (const char* place : kRecursiveStatementPlaces) {
    for (const char* spec :
         {"rec(a)", "nexttime rec(a)", "eventually [1:2] rec(a)",
          "always rec(a)", "a until rec(a)", "a until_with rec(a)", "mid(a)",
          "disable iff (a) rec(a)"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      ElabFixture f;
      ElaborateSrc(RecursiveAssertionIn(place, spec), f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

}  // namespace
