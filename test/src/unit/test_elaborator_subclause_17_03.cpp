#include <gtest/gtest.h>

#include "elaborator/checker_instantiation.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CheckerInstantiation, AllowedInConcurrentAssertionContext) {
  EXPECT_TRUE(CheckerInstantiationSiteIsLegal(
      CheckerInstantiationSite::kConcurrentAssertionContext));
}

TEST(CheckerInstantiation, IllegalInForkJoinBlocks) {
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoin));
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoinAny));
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoinNone));
}

TEST(CheckerInstantiation, IllegalInProcedureOfAnotherChecker) {
  EXPECT_FALSE(CheckerInstantiationSiteIsLegal(
      CheckerInstantiationSite::kProcedureOfAnotherChecker));
}

TEST(CheckerInstantiation, OutputActualArgMustBeVariableOrNetLvalue) {
  EXPECT_TRUE(
      CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kVariableLvalue));
  EXPECT_TRUE(
      CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kNetLvalue));
  EXPECT_FALSE(CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kOther));
}

TEST(CheckerInstantiation, AllFourPortConnectionStylesSupported) {
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kPositional));
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kNamedExplicit));
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kNamedImplicit));
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kWildcard));
}

TEST(CheckerInstantiation, DollarFormalReferencePermittedUses) {
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kCycleDelayRangeUpperBound));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kSequenceInstanceActual));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kPropertyInstanceActual));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kCheckerInstanceActual));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kNestedCheckerDefaultArg));
  EXPECT_FALSE(DollarFormalReferenceIsLegal(DollarFormalReferenceUse::kOther));
}

TEST(CheckerInstantiation, DollarActualRequiresUntypedFormalAndPermittedRefs) {
  EXPECT_TRUE(DollarActualArgumentIsLegal(true, true));
  EXPECT_FALSE(DollarActualArgumentIsLegal(false, true));
  EXPECT_FALSE(DollarActualArgumentIsLegal(true, false));
  EXPECT_FALSE(DollarActualArgumentIsLegal(false, false));
}

TEST(CheckerInstantiation, ConstCastOrAutomaticActualRestrictsFormalUsage) {
  EXPECT_TRUE(ConstCastOrAutomaticActualFormalUsageIsLegal(false, true, true));
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(true, true, false));
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(true, false, true));
  EXPECT_TRUE(ConstCastOrAutomaticActualFormalUsageIsLegal(true, false, false));
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(true, true, true));
}

TEST(CheckerInstantiation, APlainSignalBindsAnEventFormal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(logic a, event clk);\n"
      "  a1: assert property (@clk a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  chk c(a, clk);\n"
      "endmodule\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralCheckerInstantiation, AModuleCannotBeInstantiatedInAProcedure) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk, a;\n"
      "  always @(posedge clk) begin\n"
      "    leaf l(a);\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'leaf' is not a checker, and only a checker may "
                            "be instantiated in procedural code",
                            6, "17.3"));
}

TEST(ProceduralCheckerInstantiation, NotInAProcedureOfAnotherChecker) {
  ElabFixture f;
  ElaborateSrc(
      "checker inner(logic a, logic clk);\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "endchecker\n"
      "checker outer(logic a, logic clk);\n"
      "  initial begin\n"
      "    inner i(a, clk);\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk, a;\n"
      "  outer o(a, clk);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker 'inner' cannot be instantiated in "
                            "procedural code that belongs to another checker",
                            6, "17.3"));
}

TEST(ProceduralCheckerInstantiation, OneInstanceToAnInstantiation) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(logic a, logic clk);\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk) begin\n"
      "    chk c1(a, clk), c2(b, clk);\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker 'chk' is instantiated one instance to an "
                            "instantiation; 'c2' after a ',' is a second",
                            7, "A.4.1.4"));
}

TEST(ProceduralCheckerInstantiation, AnUnknownNameIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic clk, a;\n"
      "  always @(posedge clk) begin\n"
      "    nochk c(a, clk);\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unknown module 'nochk'", 4,
                            "23.3.2"));
}

TEST(ProceduralCheckerInstantiation, NotInAForkBlock) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(logic a, logic clk);\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk, a;\n"
      "  initial begin\n"
      "    fork\n"
      "      chk c1(a, clk);\n"
      "      begin chk c2(a, clk); end\n"
      "    join_none\n"
      "    chk c3(a, clk);\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  const char* const kMessage =
      "a checker instance cannot stand inside a fork-join, fork-join_any or "
      "fork-join_none block";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 8, "17.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 9, "17.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, 11, "17.3"));
}

TEST(CheckerActuals, AnOutputActualThatIsNoLvalueIsReported) {
  const char* const kReport =
      "the output actual of the formal 'failure' of checker 'c' is neither a "
      "variable nor a net lvalue";
  ElabFixture f;
  ElaborateSrc(
      "checker c(event clk, output bit failure, output bit [1:0] both);\n"
      "  a1: assert property (@clk 1) failure = 1'b0; else failure = 1'b1;\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk, f, g, h;\n"
      "  c u1(posedge clk, f & g, h);\n"
      "  c u2(.clk(posedge clk), .failure(f), .both({g, h}));\n"
      "  logic arr [2];\n"
      "  struct packed { logic x; logic y; } st;\n"
      "  c u3(posedge clk, arr[0], st);\n"
      "  c u4(posedge clk, st.x);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "neither a variable", 10, "17.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "neither a variable", 11, "17.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "17.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "neither a variable", 7, "17.3"));
}

TEST(CheckerActuals, ADollarActualOnATypedOrOperandFormalIsReported) {
  const char* const kReport =
      "which shall be untyped and referenced only as the upper bound of a "
      "cycle delay range";
  ElabFixture f;
  ElaborateSrc(
      "checker c1(int n, event clk);\n"
      "  a1: assert property (@clk 1 ##[1:n] 1);\n"
      "endchecker\n"
      "checker c2(m, event clk);\n"
      "  a1: assert property (@clk m);\n"
      "endchecker\n"
      "checker c3(k, event clk);\n"
      "  a1: assert property (@clk 1 ##[1:k] 1);\n"
      "endchecker\n"
      "checker c4(k, event clk);\n"
      "  c3 inner(k, clk);\n"
      "endchecker\n"
      "checker c5(k, event clk);\n"
      "  checker nested(j = k, event e = clk);\n"
      "  endchecker\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  c1 u1($, posedge clk);\n"
      "  c2 u2($, posedge clk);\n"
      "  c3 u3($, posedge clk);\n"
      "  c4 u4($, posedge clk);\n"
      "  c5 u5($, posedge clk);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 19, "17.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 20, "17.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 21, "17.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 22, "17.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 23, "17.3"));
}

TEST(CheckerActuals, AConstOrAutomaticActualsFormalInAnAssignIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker c(logic a);\n"
      "  logic b;\n"
      "  assign b = a;\n"
      "endchecker\n"
      "checker d(logic a, logic clk);\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk, x;\n"
      "  always @(posedge clk) begin\n"
      "    automatic logic v = x;\n"
      "    c u(v);\n"
      "    d w(v, clk);\n"
      "  end\n"
      "  c k(const'(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the formal 'a' of checker 'c', bound to an "
                            "automatic value, is used in a continuous "
                            "assignment or procedural code",
                            12, "17.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "of checker 'd', bound to",
                             13, "17.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the formal 'a' of checker 'c', bound to a const "
                            "cast, is used in a continuous assignment or "
                            "procedural code",
                            15, "17.3"));
}

}  // namespace
