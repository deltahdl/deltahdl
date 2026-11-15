#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kDollarReport =
    "which shall be untyped and referenced only as the upper bound of a "
    "cycle delay range";

size_t ErrorCount(const std::vector<Diagnostic>& diags) {
  size_t count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError) ++count;
  }
  return count;
}

void ExpectDollar(const std::string& src,
                  const std::vector<std::string>& reported,
                  const std::vector<std::string>& accepted) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  for (const auto& marker : reported) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDollarReport,
                              LineHolding(src, marker), "17.3"))
        << marker << "\n"
        << src;
  }
  for (const auto& marker : accepted) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, marker)))
        << marker << "\n"
        << src;
  }
}

void ExpectNoError(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_EQ(ErrorCount(f.diag.Diagnostics()), 0u) << src;
}

std::string Checker(const std::string& name, const std::string& formals,
                    const std::string& body) {
  return "checker " + name + "(" + formals + ");\n" + body + "endchecker\n";
}

std::string Bound(const std::string& name, const std::string& property) {
  return Checker(name, "k, event clk",
                 "  a1: assert property (@clk " + property + ");\n");
}

std::string InModule(const std::string& items) {
  return "module m;\n  logic clk, x;\n" + items + "endmodule\n";
}

const char* const kUpperBoundChecker =
    "checker ok(k, event clk);\n"
    "  a1: assert property (@clk 1 ##[1:k] 1);\n"
    "endchecker\n";

const char* const kOperandChecker =
    "checker bad(k, event clk);\n"
    "  a1: assert property (@clk k);\n"
    "endchecker\n";

TEST(CheckerDollarActual, RepetitionRangeUpperBoundsAreAccepted) {
  ExpectDollar(Checker("cr", "k, event clk, logic a",
                       "  a1: assert property (@clk a [*1:k] ##1 1);\n"
                       "  a2: assert property (@clk a [=1:k] ##1 1);\n"
                       "  a3: assert property (@clk a [->1:k] ##1 1);\n") +
                   InModule("  cr ur($, posedge clk, x);\n"),
               {}, {"cr ur("});
}

TEST(CheckerDollarActual, DISABLED_ASingleRepetitionCountIsReported) {
  ExpectDollar(Checker("c1", "k, event clk, logic a",
                       "  a1: assert property (@clk a [*k] ##1 1);\n") +
                   Checker("c2", "k, event clk, logic a",
                           "  a1: assert property (@clk a [=k] ##1 1);\n") +
                   Checker("c3", "k, event clk, logic a",
                           "  a1: assert property (@clk a [->k] ##1 1);\n") +
                   kUpperBoundChecker +
                   InModule("  c1 u1($, posedge clk, x);\n"
                            "  c2 u2($, posedge clk, x);\n"
                            "  c3 u3($, posedge clk, x);\n"
                            "  ok uo($, posedge clk);\n"),
               {"c1 u1(", "c2 u2(", "c3 u3("}, {"ok uo("});
}

TEST(CheckerDollarActual,
     DISABLED_AlwaysAndStrongEventuallyUpperBoundsAreAccepted) {
  ExpectNoError(Checker("ca", "k, logic clk",
                        "  a1: assert property (@(posedge clk) always [1:k] "
                        "1);\n") +
                Checker("ce", "k, logic clk",
                        "  a1: assert property (@(posedge clk) s_eventually "
                        "[1:k] 1);\n") +
                InModule("  ca ua($, clk);\n  ce ue($, clk);\n"));
}

TEST(CheckerDollarActual, AWholeNamedSequenceOrPropertyActualIsAccepted) {
  ExpectDollar(Checker("cs", "k, event clk",
                       "  sequence s(n);\n    1 ##[1:n] 1;\n  endsequence\n"
                       "  property p(n);\n    1 ##[1:n] 1;\n  endproperty\n"
                       "  a1: assert property (@clk s(k));\n"
                       "  a2: assert property (@clk p(k));\n") +
                   Checker("cx", "k, event clk",
                           "  sequence s(n);\n    1 ##[1:n] 1;\n  endsequence\n"
                           "  a1: assert property (@clk s(k + 1));\n") +
                   InModule("  cs us($, posedge clk);\n"
                            "  cx ux($, posedge clk);\n"),
               {"cx ux("}, {"cs us("});
}

TEST(CheckerDollarActual, AnUntypedKeywordFormalReadAsAnOperandIsReported) {
  ExpectDollar(Checker("cu", "untyped k, event clk",
                       "  a1: assert property (@clk k);\n") +
                   Checker("cv", "untyped k, event clk",
                           "  a1: assert property (@clk 1 ##[1:k] 1);\n") +
                   InModule("  cu uu($, posedge clk);\n"
                            "  cv uv($, posedge clk);\n"),
               {"cu uu("}, {"cv uv("});
}

TEST(CheckerDollarActual,
     DISABLED_ALowerBoundASingleDelayOrAnExpressionIsReported) {
  ExpectDollar(Bound("cl", "1 ##[k:5] 1") + Bound("cd", "1 ##k 1") +
                   Bound("cm", "1 ##[1:k-1] 1") + kUpperBoundChecker +
                   InModule("  cl ul($, posedge clk);\n"
                            "  cd ud($, posedge clk);\n"
                            "  cm um($, posedge clk);\n"
                            "  ok uo($, posedge clk);\n"),
               {"cl ul(", "cd ud(", "cm um("}, {"ok uo("});
}

TEST(CheckerDollarActual, AConstantRangeOrANexttimeIndexIsReported) {
  ExpectDollar(Bound("ca", "s_always [1:k] 1") +
                   Bound("ce", "eventually [1:k] 1") +
                   Bound("cn", "nexttime [k] 1") + kUpperBoundChecker +
                   InModule("  ca ua($, posedge clk);\n"
                            "  ce ue($, posedge clk);\n"
                            "  cn un($, posedge clk);\n"
                            "  ok uo($, posedge clk);\n"),
               {"ca ua(", "ce ue(", "cn un("}, {"ok uo("});
}

TEST(CheckerDollarActual, DISABLED_ALetActualIsReported) {
  ExpectDollar(Checker("cl", "k, event clk",
                       "  let L(n) = n;\n"
                       "  a1: assert property (@clk L(k));\n") +
                   kUpperBoundChecker +
                   InModule("  cl ul($, posedge clk);\n"
                            "  ok uo($, posedge clk);\n"),
               {"cl ul("}, {"ok uo("});
}

TEST(CheckerDollarActual, AContinuousAssignmentOrAProcedureIsReported) {
  ExpectDollar(
      Checker("cg", "k, logic clk", "  int b;\n  assign b = k;\n") +
          Checker("cc", "k, logic clk", "  int b;\n  always_comb b = k;\n") +
          Checker("cf", "k, logic clk",
                  "  int b;\n  always_ff @(posedge clk) b <= k;\n") +
          Checker("ci", "k, logic clk", "  initial $display(k);\n") +
          Checker("cn", "k, logic clk", "  final $display(k);\n") +
          Checker("ok", "k, logic clk",
                  "  a1: assert property (@(posedge clk) 1 ##[1:k] 1);\n") +
          InModule("  cg ug($, clk);\n"
                   "  cc uc($, clk);\n"
                   "  cf uf($, clk);\n"
                   "  ci ui($, clk);\n"
                   "  cn un($, clk);\n"
                   "  ok uo($, clk);\n"),
      {"cg ug(", "cc uc(", "cf uf(", "ci ui(", "cn un("}, {"ok uo("});
}

TEST(CheckerDollarActual,
     DISABLED_ANestedCheckerReadingItAsAnOperandIsReported) {
  ExpectDollar(
      std::string(kOperandChecker) +
          Checker("pass_on", "k, event clk", "  bad inner(k, clk);\n") +
          Checker("by_default", "k, event clk",
                  "  checker nested(j = k, event e = clk);\n"
                  "    a1: assert property (@e j);\n"
                  "  endchecker\n"
                  "  nested nn();\n") +
          InModule("  pass_on up($, posedge clk);\n"
                   "  by_default ud($, posedge clk);\n"),
      {"pass_on up(", "by_default ud("}, {});
}

TEST(CheckerDollarActual, ANestedCheckerTakingItByNameAsABoundIsAccepted) {
  ExpectDollar(std::string(kUpperBoundChecker) +
                   Checker("pass_on", "k, event clk",
                           "  ok inner(.k(k), .clk(clk));\n") +
                   InModule("  pass_on up($, posedge clk);\n"),
               {}, {"pass_on up("});
}

TEST(CheckerDollarActual, ADefaultInAnEmptySlotUsedAsABoundIsAccepted) {
  ExpectDollar(Checker("cd", "k = $, event clk",
                       "  a1: assert property (@clk 1 ##[1:k] 1);\n") +
                   InModule("  cd u1(, posedge clk);\n"
                            "  cd u2(.k(), .clk(posedge clk));\n"),
               {}, {"cd u1(", "cd u2("});
}

TEST(CheckerDollarActual,
     DISABLED_ADefaultInAnEmptySlotReadAsAnOperandIsReported) {
  ExpectDollar(
      Checker("cd", "k = $, event clk", "  a1: assert property (@clk k);\n") +
          Checker("ct", "int k = $, event clk",
                  "  a1: assert property (@clk 1 ##[1:k] 1);\n") +
          InModule("  cd u1(, posedge clk);\n"
                   "  cd u2(.k(), .clk(posedge clk));\n"
                   "  ct u3(, posedge clk);\n"),
      {"cd u1(", "cd u2(", "ct u3("}, {});
}

const char* const kDefaultOperand =
    "checker cz(logic clk, k = $);\n"
    "  a1: assert property (@(posedge clk) k);\n"
    "endchecker\n";

const char* const kDefaultBound =
    "checker cb(logic clk, k = $);\n"
    "  a1: assert property (@(posedge clk) 1 ##[1:k] 1);\n"
    "endchecker\n";

TEST(CheckerDollarActual, ADefaultForAnOmittedFormalIsCheckedLikeAnActual) {
  ExpectDollar(Checker("ct", "logic clk, int k = $",
                       "  a1: assert property (@(posedge clk) 1 ##[1:k] "
                       "1);\n") +
                   kDefaultOperand +
                   InModule("  cz u1(.clk(clk));\n"
                            "  ct u2(.clk(clk));\n"
                            "  cz u3(clk);\n"),
               {"cz u1(", "ct u2(", "cz u3("}, {});
}

TEST(CheckerDollarActual, AWildcardTakingAnOperandDefaultIsReported) {
  ExpectDollar(std::string(kDefaultOperand) + InModule("  cz u1(.*);\n"),
               {"cz u1("}, {});
}

TEST(CheckerDollarActual, DISABLED_AnOmittedFormalsBoundDefaultIsAccepted) {
  ExpectNoError(std::string(kDefaultBound) + InModule("  cb u1(.clk(clk));\n"
                                                      "  cb u2(clk);\n"
                                                      "  cb u3(.*);\n"));
}

TEST(CheckerDollarActual, ANamedConnectionIsCheckedLikeAPositionalOne) {
  ExpectDollar(Checker("ct", "int k, event clk",
                       "  a1: assert property (@clk 1 ##[1:k] 1);\n") +
                   kUpperBoundChecker +
                   InModule("  ct u1(.k($), .clk(posedge clk));\n"
                            "  ok u2(.k($), .clk(posedge clk));\n"),
               {"ct u1("}, {"ok u2("});
}

const char* const kBothCheckers =
    "checker ok(k, logic clk);\n"
    "  a1: assert property (@(posedge clk) 1 ##[1:k] 1);\n"
    "endchecker\n"
    "checker bad(k, logic clk);\n"
    "  a1: assert property (@(posedge clk) k);\n"
    "endchecker\n";

TEST(CheckerDollarActual, AnInstanceInAnInterfaceOrAProgramIsChecked) {
  for (const char* keyword : {"interface", "program"}) {
    SCOPED_TRACE(keyword);
    ExpectDollar(std::string(kBothCheckers) + keyword +
                     " box(input logic clk);\n"
                     "  ok uo($, clk);\n"
                     "  bad ub($, clk);\n"
                     "end" +
                     keyword + "\n" + InModule("  box b(clk);\n"),
                 {"bad ub("}, {"ok uo("});
  }
}

TEST(CheckerDollarActual, AnInstanceInAnotherCheckerIsChecked) {
  ExpectDollar(std::string(kBothCheckers) +
                   "checker outer(logic clk);\n"
                   "  ok uo($, clk);\n"
                   "  bad ub($, clk);\n"
                   "endchecker\n" +
                   InModule("  outer w(clk);\n"),
               {"bad ub("}, {"ok uo("});
}

TEST(CheckerDollarActual, DISABLED_AnInstanceInAGenerateBlockIsChecked) {
  ExpectDollar(std::string(kBothCheckers) + InModule("  if (1) begin : g\n"
                                                     "    ok uo($, clk);\n"
                                                     "    bad ub($, clk);\n"
                                                     "  end\n"),
               {"bad ub("}, {"ok uo("});
}

TEST(CheckerDollarActual, AProceduralInstanceIsChecked) {
  ExpectDollar(
      std::string(kBothCheckers) + InModule("  always @(posedge clk) begin\n"
                                            "    ok uo($, clk);\n"
                                            "    bad ub($, clk);\n"
                                            "  end\n"
                                            "  initial begin\n"
                                            "    ok vo($, clk);\n"
                                            "    bad vb($, clk);\n"
                                            "  end\n"),
      {"bad ub(", "bad vb("}, {"ok uo(", "ok vo("});
}

TEST(CheckerDollarActual, DISABLED_APackageCheckerNamedWithItsScopeIsChecked) {
  ExpectDollar(std::string("package pk;\n") + kBothCheckers + "endpackage\n" +
                   InModule("  pk::ok uo($, clk);\n"
                            "  pk::bad ub($, clk);\n"),
               {"pk::bad ub("}, {"pk::ok uo("});
}

}  // namespace
