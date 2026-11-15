#include <gtest/gtest.h>

#include <string>
#include <vector>

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

const char* const kInOtherChecker =
    "cannot be instantiated in procedural code that belongs to another "
    "checker";

const char* const kInForkBlock =
    "a checker instance cannot stand inside a fork-join, fork-join_any or "
    "fork-join_none block";

const char* const kInnerChecker =
    "checker inner(logic a, logic clk);\n"
    "  a1: assert property (@(posedge clk) a);\n"
    "endchecker\n";

std::string OuterHolding(const std::string& body) {
  return "checker outer(logic a, logic clk);\n"
         "  inner s(a, clk);\n" +
         body + "endchecker\n";
}

const char* const kOuterTop =
    "module top;\n"
    "  logic clk, a;\n"
    "  outer o(a, clk);\n"
    "endmodule\n";

void ExpectReportedBesideStatic(const std::string& src,
                                const std::vector<std::string>& at,
                                const char* message, const char* subclause) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  for (const auto& marker : at) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(src, marker), subclause))
        << marker << "\n"
        << src;
  }
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "inner s(")))
      << src;
}

void ExpectInOtherChecker(const std::string& body,
                          const std::vector<std::string>& at) {
  ExpectReportedBesideStatic(kInnerChecker + OuterHolding(body) + kOuterTop, at,
                             kInOtherChecker, "17.3");
}

TEST(ProceduralCheckerInstantiation, NotInACheckersAlwaysFf) {
  ExpectInOtherChecker(
      "  always_ff @(posedge clk) begin\n    inner i(a, clk);\n  end\n",
      {"inner i("});
}

TEST(ProceduralCheckerInstantiation, NotInACheckersAlwaysComb) {
  ExpectInOtherChecker("  always_comb begin\n    inner i(a, clk);\n  end\n",
                       {"inner i("});
}

TEST(ProceduralCheckerInstantiation, NotInACheckersAlwaysLatch) {
  ExpectInOtherChecker("  always_latch begin\n    inner i(a, clk);\n  end\n",
                       {"inner i("});
}

TEST(ProceduralCheckerInstantiation, NotInACheckersGeneralAlways) {
  std::string src =
      kInnerChecker +
      OuterHolding(
          "  always @(posedge clk) begin\n    inner i(a, clk);\n  end\n") +
      kOuterTop;
  ExpectReportedBesideStatic(src, {"inner i("}, kInOtherChecker, "17.3");
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_TRUE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "always @")));
}

TEST(ProceduralCheckerInstantiation, NotNestedInACheckersProcedure) {
  ExpectInOtherChecker(
      "  always_ff @(posedge clk) begin\n"
      "    if (a) inner i1(a, clk);\n"
      "    begin\n      begin inner i2(a, clk); end\n    end\n"
      "    case (a)\n      1'b1: inner i3(a, clk);\n      default: ;\n"
      "    endcase\n"
      "    for (int k = 0; k < 1; k++) inner i4(a, clk);\n"
      "  end\n",
      {"inner i1(", "inner i2(", "inner i3(", "inner i4("});
}

TEST(ProceduralCheckerInstantiation, NotInAProcedureOfACheckersGenerateBlock) {
  ExpectInOtherChecker(
      "  if (1) begin : g\n"
      "    always_ff @(posedge clk) begin\n      inner i(a, clk);\n    end\n"
      "  end\n",
      {"inner i("});
}

const char* const kForbiddenProcedure =
    "  always_ff @(posedge clk) begin\n    inner i(a, clk);\n  end\n";

TEST(ProceduralCheckerInstantiation, NotInTheProcedureOfAModulesChecker) {
  ExpectReportedBesideStatic(
      std::string(kInnerChecker) + "module top;\n  logic clk, a;\n" +
          OuterHolding(kForbiddenProcedure) + "  outer o(a, clk);\nendmodule\n",
      {"inner i("}, kInOtherChecker, "17.3");
}

TEST(ProceduralCheckerInstantiation, NotInTheProcedureOfAnInterfacesChecker) {
  ExpectReportedBesideStatic(
      std::string(kInnerChecker) +
          "interface ifc(input logic clk, input logic a);\n" +
          OuterHolding(kForbiddenProcedure) +
          "  outer o(a, clk);\nendinterface\n"
          "module top;\n  logic clk, a;\n  ifc i(clk, a);\nendmodule\n",
      {"inner i("}, kInOtherChecker, "17.3");
}

TEST(ProceduralCheckerInstantiation, NotInTheProcedureOfAProgramsChecker) {
  ExpectReportedBesideStatic(
      std::string(kInnerChecker) +
          "program prg(input logic clk, input logic a);\n" +
          OuterHolding(kForbiddenProcedure) +
          "  outer o(a, clk);\nendprogram\n"
          "module top;\n  logic clk, a;\n  prg p(clk, a);\nendmodule\n",
      {"inner i("}, kInOtherChecker, "17.3");
}

TEST(ProceduralCheckerInstantiation,
     DISABLED_NotInTheProcedureOfAPackagesChecker) {
  ExpectReportedBesideStatic(
      std::string("package p;\n") + kInnerChecker +
          OuterHolding(kForbiddenProcedure) +
          "endpackage\n"
          "module top;\n  logic clk, a;\n  p::outer o(a, clk);\nendmodule\n",
      {"inner i("}, kInOtherChecker, "17.3");
}

TEST(ProceduralCheckerInstantiation, NotInTheProcedureOfANestedChecker) {
  ExpectReportedBesideStatic(
      std::string(kInnerChecker) + "checker wrap(logic a, logic clk);\n" +
          OuterHolding(kForbiddenProcedure) +
          "  outer o(a, clk);\nendchecker\n"
          "module top;\n  logic clk, a;\n  wrap w(a, clk);\nendmodule\n",
      {"inner i("}, kInOtherChecker, "17.3");
}

TEST(ProceduralCheckerInstantiation, NotThroughAPackageScope) {
  ExpectReportedBesideStatic(
      std::string("package p;\n") + kInnerChecker + "endpackage\n" +
          "checker outer(logic a, logic clk);\n"
          "  p::inner s(a, clk);\n"
          "  always_ff @(posedge clk) begin\n    p::inner i(a, clk);\n"
          "  end\nendchecker\n" +
          kOuterTop,
      {"p::inner i("}, kInOtherChecker, "17.3");
}

TEST(ProceduralCheckerInstantiation, NotOfACheckerDeclaredInsideIt) {
  ExpectReportedBesideStatic(
      std::string("checker outer(logic a, logic clk);\n") + kInnerChecker +
          "  inner s(a, clk);\n" + kForbiddenProcedure + "endchecker\n" +
          kOuterTop,
      {"inner i("}, kInOtherChecker, "17.3");
}

const char* const kForkChecker =
    "checker chk(logic a, logic clk);\n"
    "  a1: assert property (@(posedge clk) a);\n"
    "endchecker\n";

void ExpectForkReported(const std::string& src,
                        const std::vector<std::string>& reported,
                        const std::vector<std::string>& accepted) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  for (const auto& marker : reported) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kInForkBlock,
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

std::string ForkTop(const std::string& items) {
  return std::string(kForkChecker) + "module top;\n  logic clk, a;\n" + items +
         "endmodule\n";
}

TEST(ProceduralCheckerInstantiation, NotInAForkJoinOrForkJoinAny) {
  ExpectForkReported(ForkTop("  initial begin\n"
                             "    fork\n"
                             "      chk c1(a, clk);\n"
                             "      begin chk c2(a, clk); end\n"
                             "    join\n"
                             "    chk c3(a, clk);\n"
                             "    fork\n"
                             "      chk c4(a, clk);\n"
                             "      begin chk c5(a, clk); end\n"
                             "    join_any\n"
                             "    chk c6(a, clk);\n"
                             "  end\n"),
                     {"chk c1(", "chk c2(", "chk c4(", "chk c5("},
                     {"chk c3(", "chk c6("});
}

TEST(ProceduralCheckerInstantiation, NotUnderAnIfOrInANestedFork) {
  ExpectForkReported(ForkTop("  initial begin\n"
                             "    fork\n"
                             "      if (a) chk c1(a, clk);\n"
                             "      fork\n"
                             "        chk c2(a, clk);\n"
                             "      join\n"
                             "    join_none\n"
                             "    chk c3(a, clk);\n"
                             "  end\n"),
                     {"chk c1(", "chk c2("}, {"chk c3("});
}

const char* const kForkThenAfter =
    "begin\n"
    "    fork\n"
    "      chk c1(a, clk);\n"
    "    join_none\n"
    "    chk c2(a, clk);\n"
    "  end\n";

TEST(ProceduralCheckerInstantiation, NotInAForkOfAnAlways) {
  ExpectForkReported(
      ForkTop(std::string("  always @(posedge clk) ") + kForkThenAfter),
      {"chk c1("}, {"chk c2("});
}

TEST(ProceduralCheckerInstantiation, NotInAForkOfAGenerateBlocksInitial) {
  ExpectForkReported(ForkTop(std::string("  if (1) begin : g\n  initial ") +
                             kForkThenAfter + "  end\n"),
                     {"chk c1("}, {"chk c2("});
}

TEST(ProceduralCheckerInstantiation, NotInAForkOfAnInterfaceOrProgram) {
  for (const char* keyword : {"interface", "program"}) {
    SCOPED_TRACE(keyword);
    ExpectForkReported(
        std::string(kForkChecker) + keyword +
            " box(input logic clk, input logic a);\n  initial " +
            kForkThenAfter + "end" + keyword +
            "\nmodule top;\n  logic clk, a;\n  box b(clk, a);\nendmodule\n",
        {"chk c1("}, {"chk c2("});
  }
}

}  // namespace
