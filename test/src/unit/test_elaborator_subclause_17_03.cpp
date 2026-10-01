#include <gtest/gtest.h>

#include "elaborator/checker_instantiation.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CheckerInstantiation, AllowedInConcurrentAssertionContext) {
  // §17.3: a checker may be instantiated wherever a concurrent assertion may
  // appear.
  EXPECT_TRUE(CheckerInstantiationSiteIsLegal(
      CheckerInstantiationSite::kConcurrentAssertionContext));
}

TEST(CheckerInstantiation, IllegalInForkJoinBlocks) {
  // §17.3: it is illegal to instantiate checkers in fork-join, fork-join_any,
  // or fork-join_none blocks.
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoin));
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoinAny));
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoinNone));
}

TEST(CheckerInstantiation, IllegalInProcedureOfAnotherChecker) {
  // §17.3: it is illegal to instantiate a checker in a procedure of another
  // checker.
  EXPECT_FALSE(CheckerInstantiationSiteIsLegal(
      CheckerInstantiationSite::kProcedureOfAnotherChecker));
}

TEST(CheckerInstantiation, OutputActualArgMustBeVariableOrNetLvalue) {
  // §17.3: each checker actual output argument shall be a variable_lvalue or a
  // net_lvalue.
  EXPECT_TRUE(
      CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kVariableLvalue));
  EXPECT_TRUE(
      CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kNetLvalue));
  EXPECT_FALSE(CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kOther));
}

TEST(CheckerInstantiation, AllFourPortConnectionStylesSupported) {
  // §17.3: formal arguments may be connected like module ports, using
  // positional, fully explicit named, implicit named, and wildcard styles.
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
  // §17.3: a reference of a formal bound to `$` is legal only as a cycle-delay
  // range upper bound, an actual to a sequence/property/checker instance, or a
  // nested checker default argument.
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
  // §17.3: when `$` is an actual input argument, the corresponding formal shall
  // be untyped and each of its references shall be a permitted use.
  EXPECT_TRUE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/true,
                                  /*all_formal_references_permitted=*/true));
  EXPECT_FALSE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/false,
                                  /*all_formal_references_permitted=*/true));
  EXPECT_FALSE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/true,
                                  /*all_formal_references_permitted=*/false));
  EXPECT_FALSE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/false,
                                  /*all_formal_references_permitted=*/false));
}

TEST(CheckerInstantiation, ConstCastOrAutomaticActualRestrictsFormalUsage) {
  // §17.3: an actual input argument carrying a const cast or automatic value
  // from procedural code forbids using the formal in a continuous assignment or
  // in the checker's procedural code.
  EXPECT_TRUE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/false,
      /*formal_used_in_continuous_assignment=*/true,
      /*formal_used_in_procedural_code=*/true));
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/true,
      /*formal_used_in_procedural_code=*/false));
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/false,
      /*formal_used_in_procedural_code=*/true));
  EXPECT_TRUE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/false,
      /*formal_used_in_procedural_code=*/false));
  // Edge: both forbidden usages present at once is still rejected.
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/true,
      /*formal_used_in_procedural_code=*/true));
}

// §17.2 and §17.3: a checker formal of type event takes any event expression,
// a plain signal among them, its actual substituted rather than assigned, so
// §23.3.3's assignment compatibility, a module port's rule, does not apply.
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

// §17.3: only a checker may stand where a concurrent assertion may, so a
// module instantiated in an always procedure is refused.
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

// §17.3: a checker shall not be instantiated in a procedure of another
// checker.
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
                            "checker 'inner' shall not be instantiated in a "
                            "procedure of another checker",
                            6, "17.3"));
}

// A.4.1.4: a checker instantiated in a procedure is held to the one instance
// a checker_instantiation names, as one written as a module item is.
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

// §17.3 with §23.3.2: an instantiation in a procedure naming no design
// element is reported as one written as a module item is.
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

}  // namespace
