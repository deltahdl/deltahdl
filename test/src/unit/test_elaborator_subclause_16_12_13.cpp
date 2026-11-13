#include <gtest/gtest.h>

#include <string>

#include "elaborator/eventually_range.h"
#include "fixture_elaborator.h"
#include "helpers_bracketed_operand_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EventuallyRange, WeakEventuallyAllowsBoundedRange) {
  EXPECT_TRUE(IsEventuallyRangeWellFormed(MakeEventuallyBound(5), false));
}

TEST(EventuallyRange, WeakEventuallyRejectsUnboundedMaximum) {
  EXPECT_FALSE(IsEventuallyRangeWellFormed(MakeEventuallyDollar(), false));
}

TEST(EventuallyRange, StrongEventuallyAllowsUnboundedMaximum) {
  EXPECT_TRUE(IsEventuallyRangeWellFormed(MakeEventuallyDollar(), true));
}

TEST(EventuallyRangeElaboration, ANegativeParameterBoundIsReported) {
  const char* const kReport =
      "eventually range bounds shall be non-negative integer constant "
      "expressions, the minimum no greater than the maximum";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  localparam int NEG = -1, HI = 2;\n"
      "  a1: assert property (@(posedge clk) s_eventually [NEG:HI] a);\n"
      "  a2: assert property (@(posedge clk) s_eventually [0:HI] a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.12.13"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.13"));
}

constexpr const char* kRangeReport = "eventually range";

constexpr const char* kBoundedReport = "weak eventually needs a finite range";

constexpr const char* kForbiddenWeakRanges[] = {
    "-1:2", "0:-1",   "3:1",      "NEG:2",    "0:NEG", "LO:HI", "k:2",
    "0:k",  "1.5:2",  "0:2.5",    "R:3",      "1:R",   "R:R",   "S:3",
    "1:S",  "2'd3:1", "2'sb11:1", "0:2'sb11", "1+4:2", "0-1:2"};

constexpr const char* kAllowedRanges[] = {"0:2",         "3:3",    "0:0",
                                          "ONE:2",       "2'd1:3", "int'(R):2",
                                          "0:$clog2(4)", "(1):(2)"};

constexpr const char* kUnboundedRanges[] = {"0:$", "2:$", "ONE:$"};

constexpr const char* kAllowedStrongRanges[] = {"0:$", "2:$", "ONE:$", "0:2",
                                                "3:3"};

void ExpectRangeReported(const std::string& src) {
  ExpectOperandReported(src, kRangeReport, "16.12.13");
}

void ExpectUnboundedReported(const std::string& src) {
  ExpectOperandReported(src, kBoundedReport, "16.12.13");
}

TEST(EventuallyRangeElaboration,
     DISABLED_ABadWeakRangeInAnAssertionStatementIsReportedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"eventually"}, kForbiddenWeakRanges,
                 BracketedStatement, ExpectRangeReported);
}

TEST(EventuallyRangeElaboration,
     DISABLED_ABadWeakRangeInAPropertyDeclarationIsReportedInEachPlace) {
  ForEachOperand(kOperandDeclarationPlaces, {"eventually"},
                 kForbiddenWeakRanges, BracketedDeclaration,
                 ExpectRangeReported);
}

TEST(EventuallyRangeElaboration, AGoodRangeIsAcceptedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"eventually", "s_eventually"},
                 kAllowedRanges, BracketedStatement, ExpectOperandAccepted);
  ForEachOperand(kOperandDeclarationPlaces, {"eventually", "s_eventually"},
                 kAllowedRanges, BracketedDeclaration, ExpectOperandAccepted);
}

TEST(EventuallyRangeElaboration,
     DISABLED_AnUnboundedWeakRangeInAnAssertionStatementIsReported) {
  ForEachOperand(kOperandStatementPlaces, {"eventually"}, kUnboundedRanges,
                 BracketedStatement, ExpectUnboundedReported);
}

TEST(EventuallyRangeElaboration,
     DISABLED_AnUnboundedWeakRangeInAPropertyDeclarationIsReported) {
  ForEachOperand(kOperandDeclarationPlaces, {"eventually"}, kUnboundedRanges,
                 BracketedDeclaration, ExpectUnboundedReported);
}

TEST(EventuallyRangeElaboration, AnUnboundedStrongRangeIsAcceptedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"s_eventually"},
                 kAllowedStrongRanges, BracketedStatement,
                 ExpectOperandAccepted);
  ForEachOperand(kOperandDeclarationPlaces, {"s_eventually"},
                 kAllowedStrongRanges, BracketedDeclaration,
                 ExpectOperandAccepted);
}

TEST(EventuallyRangeElaboration,
     DISABLED_ABadWeakRangeIsReportedInEveryDirective) {
  for (const char* range : {"3:1", "-1:2", "2:$"}) {
    for (const std::string& target :
         OperandDirectives(std::string("eventually [") + range + "] a")) {
      SCOPED_TRACE(target);
      ExpectOperandReported(
          OperandIn("module", target),
          std::string(range) == "2:$" ? kBoundedReport : kRangeReport,
          "16.12.13");
    }
  }
}

std::string NestedStatement(const std::string& op, const std::string& range) {
  return "a1: assert property (@(posedge clk) a |-> " + op + " [" + range +
         "] a);";
}

TEST(EventuallyRangeElaboration,
     DISABLED_ANestedUnboundedWeakRangeIsReportedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"eventually"}, kUnboundedRanges,
                 NestedStatement, ExpectUnboundedReported);
}

TEST(EventuallyRangeElaboration,
     ANestedUnboundedStrongRangeIsAcceptedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"s_eventually"}, kUnboundedRanges,
                 NestedStatement, ExpectOperandAccepted);
}

TEST(EventuallyRangeElaboration, AGoodRangeIsAcceptedInEveryDirective) {
  for (const char* spec :
       {"eventually [1:2] a", "s_eventually [1:$] a", "s_eventually a"}) {
    for (const std::string& target : OperandDirectives(spec)) {
      SCOPED_TRACE(target);
      ExpectOperandAccepted(OperandIn("module", target));
    }
  }
}

TEST(EventuallyRangeElaboration,
     DISABLED_ABadActualForAFormalWeakRangeIsReported) {
  for (const char* actuals :
       {"-1, 2", "0, -1", "3, 1", "NEG, 2", "LO, HI", "k, 2", "0, k", "1.5, 2",
        "R, 3", "1, R", "S, 3"}) {
    SCOPED_TRACE(actuals);
    ExpectOperandReported(
        FormalOperandSource("lo, hi", "eventually [lo:hi]", actuals),
        kRangeReport, "16.12.13", kOperandLine + 1);
  }
}

TEST(EventuallyRangeElaboration, AGoodActualForAFormalRangeIsAccepted) {
  for (const char* actuals : {"0, 2", "3, 3", "ONE, HI", "int'(R), 2"}) {
    for (const char* op : {"eventually", "s_eventually"}) {
      SCOPED_TRACE(std::string(op) + " " + actuals);
      ExpectOperandAccepted(
          FormalOperandSource("lo, hi", std::string(op) + " [lo:hi]", actuals));
    }
  }
}

TEST(EventuallyRangeElaboration,
     DISABLED_ADollarActualForAFormalStrongMaximumIsAccepted) {
  ExpectOperandAccepted(
      FormalOperandSource("lo, hi", "s_eventually [lo:hi]", "1, $"));
}

std::string DollarParameterSource(const std::string& parameter,
                                  const std::string& op) {
  return "module m;\n"
         "  bit clk, a;\n"
         "  localparam " +
         parameter +
         ";\n"
         "  a1: assert property (@(posedge clk) " +
         op +
         " [1:P] a);\n"
         "  property q; @(posedge clk) " +
         op + " [1:P] a; endproperty\n" + "endmodule\n";
}

TEST(EventuallyRangeElaboration,
     DISABLED_AnUnboundedParameterMaximumOfAWeakRangeIsReported) {
  const std::string kSrc = DollarParameterSource("P = $", "eventually");
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kBoundedReport, 4, "16.12.13"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kBoundedReport, 5, "16.12.13"));
}

TEST(EventuallyRangeElaboration, ABoundedOrStrongParameterMaximumIsAccepted) {
  ExpectOperandAccepted(DollarParameterSource("int P = 4", "eventually"));
  ExpectOperandAccepted(DollarParameterSource("P = $", "s_eventually"));
}

std::string OverriddenParameterSource(const std::string& op,
                                      const std::string& value) {
  return "module c #(parameter P = 3) (input logic clk, a);\n"
         "  a1: assert property (@(posedge clk) " +
         op +
         " [1:P] a);\n"
         "endmodule\n"
         "module m;\n"
         "  bit clk, a;\n"
         "  c #(.P(" +
         value +
         ")) u(clk, a);\n"
         "endmodule\n";
}

TEST(EventuallyRangeElaboration,
     DISABLED_AParameterOverriddenToDollarInAWeakRangeIsReported) {
  ElabFixture f;
  ElaborateSrc(OverriddenParameterSource("eventually", "$"), f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kBoundedReport, 2, "16.12.13"));
}

TEST(EventuallyRangeElaboration, AParameterOverriddenToAFiniteValueIsAccepted) {
  ExpectOperandAccepted(OverriddenParameterSource("eventually", "5"));
  ExpectOperandAccepted(OverriddenParameterSource("s_eventually", "$"));
}

TEST(EventuallyRangeElaboration,
     DISABLED_AWeakEventuallyWithoutARangeIsReportedInEachPlace) {
  ExpectInEachPlace("eventually a", ExpectGrammarReported);
}

TEST(EventuallyRangeElaboration,
     AStrongEventuallyWithoutARangeIsAcceptedInEachPlace) {
  ExpectInEachPlace("s_eventually a", ExpectOperandAccepted);
}

}  // namespace
