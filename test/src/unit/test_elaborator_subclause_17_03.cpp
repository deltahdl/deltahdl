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

// §17.3: procedural code inside one checker cannot instantiate another
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
                            "checker 'inner' cannot be instantiated in "
                            "procedural code that belongs to another checker",
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

// §17.3: no checker instance may stand inside a fork-join, fork-join_any or
// fork-join_none block, a block nested in the fork among its statements;
// one standing after the join is a procedural checker instance as usual.
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

// §17.3: each output actual of a checker instance is a variable or net
// lvalue: f & g is neither, while h and the concatenation {g, h} are.
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "17.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "neither a variable", 7, "17.3"));
}

// §17.3: a $ actual binds an untyped formal the checker reads only as a
// range's upper bound, an instance's actual or a nested checker's default:
// c1's n is typed and c2 reads m as an operand, while c3, c4 and c5 use k as
// a bound, as an instance's actual and as a nested checker's default.
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

// §17.3: a formal bound to an actual holding a const cast or an automatic
// value is used in no continuous assignment and no procedural code of the
// checker: c assigns its formal a, while d reads its formal in an assertion
// alone.
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
