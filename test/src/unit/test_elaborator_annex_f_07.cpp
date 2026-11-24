#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(RecursivePropertyDependencyDigraph,
     RecursiveIffInStronglyConnectedComponent) {
  PropertyRegistry reg;
  ModuleItem p1;
  p1.kind = ModuleItemKind::kPropertyDecl;
  p1.name = "p1";
  p1.prop_instance_refs = {"p2", "p3"};
  ModuleItem p2;
  p2.kind = ModuleItemKind::kPropertyDecl;
  p2.name = "p2";
  ModuleItem p3;
  p3.kind = ModuleItemKind::kPropertyDecl;
  p3.name = "p3";
  p3.prop_instance_refs = {"p1"};
  reg.Register(&p1);
  reg.Register(&p2);
  reg.Register(&p3);

  EXPECT_TRUE(reg.IsRecursiveProperty(&p1));
  EXPECT_TRUE(reg.IsRecursiveProperty(&p3));
  EXPECT_FALSE(reg.IsRecursiveProperty(&p2));
}

TEST(RecursivePropertyDependencyDigraph,
     ReachabilityToRecursivePropertyIsTransitive) {
  PropertyRegistry reg;
  ModuleItem rec;
  rec.kind = ModuleItemKind::kPropertyDecl;
  rec.name = "rec";
  rec.prop_instance_refs = {"rec"};
  ModuleItem mid;
  mid.kind = ModuleItemKind::kPropertyDecl;
  mid.name = "mid";
  mid.prop_instance_refs = {"rec"};
  ModuleItem unrelated;
  unrelated.kind = ModuleItemKind::kPropertyDecl;
  unrelated.name = "unrelated";
  reg.Register(&rec);
  reg.Register(&mid);
  reg.Register(&unrelated);

  EXPECT_FALSE(reg.IsRecursiveProperty(&mid));
  EXPECT_TRUE(reg.ReachesRecursiveProperty(&mid));
  EXPECT_FALSE(reg.ReachesRecursiveProperty(&unrelated));
}

TEST(RecursivePropertyRestrictionEnforcement,
     NotOnPropertyReachingRecursiveRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property mid(p);\n"
      "    rec(p);\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    not mid(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "negation or strong operator applied to property \"mid\"",
                    8, "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement,
     DisableIffInRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic rst);\n"
      "  property rec(p);\n"
      "    disable iff (rst)\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "recursive property \"rec\" may not use disable iff (Restriction 2)", 2,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement, ZeroWeightSelfCycleRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |-> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive property \"rec\" lies on a recursion "
                            "cycle with no positive advance in time",
                            2, "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement, PositiveWeightSelfCycleAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictionEnforcement, ZeroWeightMutualCycleRejected) {
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
                            "cycle with no positive advance in time",
                            2, "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement,
     PositiveWeightMutualCycleAllowed) {
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

TEST(RecursivePropertyRestrictionEnforcement,
     RecursiveArgumentToNonLocalFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property fib (int a, b, n, fib_sig);\n"
      "    (n > 0) |->\n"
      "    ((fib_sig == a) and (1'b1 |=> fib(b, a + b, n - 1, fib_sig)));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive instance of \"fib\" passes an actual "
                            "argument that contains a formal of \"fib\"",
                            2, "16.12.17"));
}

constexpr const char* kStall =
    "lies on a recursion cycle with no positive advance in time "
    "(Restriction 3)";
constexpr const char* kNegated =
    "which reaches a recursive property (Restriction 1)";
constexpr const char* kRec =
    "property rec(p); p and (1'b1 |=> rec(p)); endproperty";
constexpr const char* kPackage =
    "package pk;\n"
    "  property rec(p); p and (1'b1 |=> rec(p)); endproperty\n"
    "  property leaf(p); p; endproperty\n"
    "endpackage\n";

std::vector<std::string> TimedThreeCycle() {
  return {"property r1(p); p and (1'b1 |=> r2(p)); endproperty",
          "property r2(p); p and r3(p); endproperty",
          "property r3(p); p and r1(p); endproperty"};
}

std::vector<std::string> WorkedExample(const std::string& implication,
                                       const std::string& p2_prefix,
                                       const std::string& p3_prefix) {
  std::string p1 = "property p1(v); v ";
  p1 += implication;
  p1 += " p2(p3()); endproperty";
  std::string p2 = "property p2(v); ";
  p2 += p2_prefix;
  p2 += "a or (1'b1 ";
  p2 += implication;
  p2 += " v); endproperty";
  std::string p3 = "property p3; ";
  p3 += p3_prefix;
  p3 += "p1(a && b); endproperty";
  return {p1, p2, p3};
}

std::vector<Diagnostic> Diagnose(const std::vector<std::string>& lines,
                                 const std::string& prefix = "") {
  std::string src = prefix;
  src += "module m(input logic a, b, c, d);\n";
  for (const auto& line : lines) {
    src += "  ";
    src += line;
    src += "\n";
  }
  src += "endmodule\n";
  ElabFixture f;
  Elaborate(src, f);
  return f.diag.Diagnostics();
}

std::string ErrorsOf(const std::vector<Diagnostic>& diags) {
  std::string out;
  for (const auto& diag : diags) {
    if (diag.severity != DiagSeverity::kError) continue;
    out += std::to_string(diag.loc.line);
    out += ": ";
    out += diag.message;
    out += "\n";
  }
  return out;
}

void ExpectAccepted(const std::vector<std::string>& lines,
                    const std::string& prefix = "") {
  EXPECT_EQ(ErrorsOf(Diagnose(lines, prefix)), "");
}

void ExpectReported(const std::vector<std::string>& lines,
                    const std::string& message, uint32_t line,
                    const std::string& prefix = "") {
  EXPECT_TRUE(
      ReportedError(Diagnose(lines, prefix), message, line, "16.12.17"));
}

bool Mentions(const std::vector<Diagnostic>& diags,
              const std::string& message) {
  for (const auto& diag : diags) {
    if (diag.message.find(message) != std::string::npos) return true;
  }
  return false;
}

TEST(RecursivePropertyActuals, AnActualOverModuleSignalsIsAccepted) {
  ExpectAccepted(
      {"property rec(p, q); p and (1'b1 |=> rec(p, c && d)); endproperty"});
}

TEST(RecursivePropertyActuals, AFormalBesideALocalBoundExpressionIsAccepted) {
  ExpectAccepted(
      {"property rec(p, local input int n); p and (1'b1 |=> rec(p, n + 1)); "
       "endproperty"});
}

TEST(RecursivePropertyActuals,
     DISABLED_AnInstanceInANonrecursiveCallerIsExempt) {
  ExpectAccepted(
      {"property rec(p, int n); p and (1'b1 |=> rec(p, n)); endproperty",
       "property top(int n); rec(a, n + 1); endproperty"});
}

TEST(RecursivePropertyActuals,
     DISABLED_AnInstanceTakingARecursiveActualIsExempt) {
  ExpectAccepted({kRec, "property leaf(q); q; endproperty",
                  "property top(p); leaf(rec(p)); endproperty"});
}

TEST(RecursivePropertyWeights, AOneCycleDelayAheadOfTheInstanceAdvancesTime) {
  ExpectAccepted({"property rec(p); 1'b1 ##1 p |-> rec(p); endproperty"});
}

TEST(RecursivePropertyWeights,
     DISABLED_AZeroCycleDelayAheadOfTheInstanceAddsNoTime) {
  ExpectReported({"property rec(p); 1'b1 ##0 p |-> rec(p); endproperty"},
                 kStall, 2);
}

TEST(RecursivePropertyWeights, ARangeFromOneAheadOfTheInstanceAdvancesTime) {
  ExpectAccepted({"property rec(p); 1'b1 ##[1:2] p |-> rec(p); endproperty"});
}

TEST(RecursivePropertyWeights,
     DISABLED_ARangeFromZeroAheadOfTheInstanceAddsNoTime) {
  ExpectReported({"property rec(p); 1'b1 ##[0:1] p |-> rec(p); endproperty"},
                 kStall, 2);
}

TEST(RecursivePropertyWeights, AnEdgeWhoseInstancesAreAllTimedAdvancesTime) {
  ExpectAccepted(
      {"property r1(p); (1'b1 |=> r2(p)) and (1'b1 |=> r2(p)); endproperty",
       "property r2(p); p and r1(p); endproperty"});
}

TEST(RecursivePropertyWeights, DISABLED_AnEdgeWeighsItsLightestInstance) {
  ExpectReported({"property r1(p); (1'b1 |=> r2(p)) and r2(p); endproperty",
                  "property r2(p); p and r1(p); endproperty"},
                 kStall, 2);
}

TEST(RecursivePropertyWeights, AThreePropertyCycleNeedsOneTimedEdge) {
  ExpectAccepted(TimedThreeCycle());
  ExpectReported({"property r1(p); p and r2(p); endproperty",
                  "property r2(p); p and r3(p); endproperty",
                  "property r3(p); p and r1(p); endproperty"},
                 kStall, 2);
}

TEST(RecursivePropertyWeights, AnActualPlacedAfterATimedImplicationAdvances) {
  ExpectAccepted(WorkedExample("|=>", "", ""));
}

TEST(RecursivePropertyWeights,
     DISABLED_AnActualPlacedAfterAnOverlappingImplicationAddsNoTime) {
  auto diags = Diagnose(WorkedExample("|->", "", ""));
  EXPECT_TRUE(ReportedError(diags, kStall, 2, "16.12.17"));
  EXPECT_TRUE(ReportedError(diags, kStall, 4, "16.12.17"));
}

TEST(RecursivePropertyWeights,
     DISABLED_AnInstanceTakesTheWeightAWrapperGivesIt) {
  ExpectAccepted({"property wrap(q); 1'b1 |=> q; endproperty",
                  "property rec(p); p and wrap(rec(p)); endproperty"});
  ExpectReported({"property wrap(q); q; endproperty",
                  "property rec(p); p and wrap(rec(p)); endproperty"},
                 kStall, 3);
}

TEST(RecursivePropertyDigraph, EveryPropertyOnAThreePropertyCycleIsRecursive) {
  auto diags = Diagnose(
      {"property r1(p); disable iff (b) p and (1'b1 |=> r2(p)); endproperty",
       "property r2(p); disable iff (b) p and r3(p); endproperty",
       "property r3(p); disable iff (b) p and r1(p); endproperty",
       "property top(p); disable iff (b) r1(p); endproperty"});
  for (const char* name : {"r1", "r2", "r3"}) {
    std::string message = "recursive property \"";
    message += name;
    message += "\" may not use disable iff";
    EXPECT_TRUE(Mentions(diags, message)) << name;
  }
  EXPECT_FALSE(Mentions(diags, "\"top\" may not use disable iff"));
}

TEST(RecursivePropertyDigraph, AnActualInstanceIsAnEdgeOfItsInstantiator) {
  EXPECT_TRUE(ReportedError(
      Diagnose(WorkedExample("|=>", "", "disable iff (b) ")),
      "recursive property \"p3\" may not use disable iff", 4, "16.12.17"));
}

TEST(RecursivePropertyDigraph, DISABLED_AnActualInstanceIsNoEdgeOfTheCallee) {
  EXPECT_FALSE(Mentions(Diagnose(WorkedExample("|=>", "disable iff (b) ", "")),
                        "\"p2\" may not use disable iff"));
}

TEST(RecursivePropertyDigraph, AnEdgeReachesAnImportedPackageProperty) {
  EXPECT_TRUE(ReportedError(
      Diagnose({"import pk::*;", "property bad(p); not rec(p); endproperty"},
               kPackage),
      kNegated, 7, "16.12.17"));
  ExpectAccepted({"import pk::*;", "property ok(p); not leaf(p); endproperty"},
                 kPackage);
}

TEST(RecursivePropertyDigraph,
     DISABLED_AnEdgeReachesAQualifiedPackageProperty) {
  ExpectReported({"property bad(p); not pk::rec(p); endproperty"}, kNegated, 6,
                 kPackage);
  ExpectAccepted({"property ok(p); not pk::leaf(p); endproperty"}, kPackage);
}

TEST(RecursivePropertyNegation,
     DISABLED_NotOverACompoundHoldingAnInstanceIsReported) {
  ExpectReported({kRec, "property bad(p); not (p and rec(p)); endproperty"},
                 kNegated, 3);
  ExpectReported(
      {kRec, "property bad(p); not (p or (1'b1 |=> rec(p))); endproperty"},
      kNegated, 3);
}

TEST(RecursivePropertyNegation,
     DISABLED_NotOverAnInstanceTakingARecursiveActualIsReportedOnce) {
  auto diags = Diagnose({kRec, "property leaf(q); q; endproperty",
                         "property bad(p); not leaf(rec(p)); endproperty"});
  EXPECT_TRUE(ReportedError(diags, "(Restriction 1)", 4, "16.12.17"));
  std::size_t errors = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError) ++errors;
  }
  EXPECT_EQ(errors, 1u) << ErrorsOf(diags);
}

TEST(RecursivePropertyNegation, NotOverAPropertyOnAThreePropertyCycle) {
  auto lines = TimedThreeCycle();
  lines.emplace_back("property bad(p); not r1(p); endproperty");
  ExpectReported(lines, kNegated, 5);
}

TEST(RecursivePropertyNegation, NotBesideARecursiveInstanceIsAccepted) {
  ExpectAccepted({kRec, "property ok(p); (not p) and rec(p); endproperty"});
}

}  // namespace
