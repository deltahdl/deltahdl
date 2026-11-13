#include <gtest/gtest.h>

#include <string>

#include "elaborator/always_range.h"
#include "fixture_elaborator.h"
#include "helpers_bracketed_operand_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AlwaysRange, BoundedNonNegativeRangeIsWellFormed) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(3)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, EqualBoundsAreWellFormed) {
  AlwaysRange range{MakeAlwaysBound(2), MakeAlwaysBound(2)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, WeakAlwaysAllowsUnboundedMaximum) {
  AlwaysRange range{MakeAlwaysBound(1), MakeAlwaysDollar()};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, StrongAlwaysRejectsUnboundedMaximum) {
  AlwaysRange range{MakeAlwaysBound(1), MakeAlwaysDollar()};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, true));
}

TEST(AlwaysRange, StrongAlwaysAcceptsBoundedRange) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(4)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, true));
}

TEST(AlwaysRange, MinimumGreaterThanMaximumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(5), MakeAlwaysBound(2)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NegativeMinimumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(-1), MakeAlwaysBound(3)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NegativeMaximumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(-2)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NonConstantBoundIsRejected) {
  AlwaysRangeBound non_constant;
  non_constant.is_constant = false;
  non_constant.is_integer = true;
  non_constant.value = 2;
  AlwaysRange range{non_constant, MakeAlwaysBound(4)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NonIntegerBoundIsRejected) {
  AlwaysRangeBound non_integer;
  non_integer.is_constant = true;
  non_integer.is_integer = false;
  non_integer.value = 1;
  AlwaysRange range{MakeAlwaysBound(0), non_integer};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRangeElaboration, AParameterRangeIsChecked) {
  const char* const kReport =
      "always range bounds shall be non-negative integer constant "
      "expressions, the minimum no greater than the maximum";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  localparam int LO = 4, HI = 2;\n"
      "  a1: assert property (@(posedge clk) always [LO:HI] a);\n"
      "  a2: assert property (@(posedge clk) always [HI:LO] a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.12.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.11"));
}

constexpr const char* kRangeReport = "always range";

constexpr const char* kBoundedReport = "s_always needs a finite range";

constexpr const char* kForbiddenStrongRanges[] = {
    "-1:2", "0:-1",   "3:1",      "NEG:2",    "0:NEG", "LO:HI", "k:2",
    "0:k",  "1.5:2",  "0:2.5",    "R:3",      "1:R",   "R:R",   "S:3",
    "1:S",  "2'd3:1", "2'sb11:1", "0:2'sb11", "1+4:2", "0-1:2"};

constexpr const char* kAllowedStrongRanges[] = {
    "0:2",    "3:3",       "0:0",         "ONE:2",
    "2'd1:3", "int'(R):2", "0:$clog2(4)", "(1):(2)"};

constexpr const char* kUnboundedRanges[] = {"0:$", "2:$", "ONE:$"};

constexpr const char* kAllowedWeakRanges[] = {"0:$", "2:$", "ONE:$", "0:2",
                                              "3:3"};

void ExpectRangeReported(const std::string& src) {
  ExpectOperandReported(src, kRangeReport, "16.12.11");
}

void ExpectUnboundedReported(const std::string& src) {
  ExpectOperandReported(src, kBoundedReport, "16.12.11");
}

TEST(AlwaysRangeElaboration,
     DISABLED_ABadStrongRangeInAnAssertionStatementIsReportedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"s_always"}, kForbiddenStrongRanges,
                 BracketedStatement, ExpectRangeReported);
}

TEST(AlwaysRangeElaboration,
     DISABLED_ABadStrongRangeInAPropertyDeclarationIsReportedInEachPlace) {
  ForEachOperand(kOperandDeclarationPlaces, {"s_always"},
                 kForbiddenStrongRanges, BracketedDeclaration,
                 ExpectRangeReported);
}

TEST(AlwaysRangeElaboration, AGoodStrongRangeIsAcceptedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"s_always", "always"},
                 kAllowedStrongRanges, BracketedStatement,
                 ExpectOperandAccepted);
  ForEachOperand(kOperandDeclarationPlaces, {"s_always", "always"},
                 kAllowedStrongRanges, BracketedDeclaration,
                 ExpectOperandAccepted);
}

TEST(AlwaysRangeElaboration,
     DISABLED_AnUnboundedStrongRangeInAnAssertionStatementIsReported) {
  ForEachOperand(kOperandStatementPlaces, {"s_always"}, kUnboundedRanges,
                 BracketedStatement, ExpectUnboundedReported);
}

TEST(AlwaysRangeElaboration,
     DISABLED_AnUnboundedStrongRangeInAPropertyDeclarationIsReported) {
  ForEachOperand(kOperandDeclarationPlaces, {"s_always"}, kUnboundedRanges,
                 BracketedDeclaration, ExpectUnboundedReported);
}

TEST(AlwaysRangeElaboration, AnUnboundedWeakRangeIsAcceptedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"always"}, kAllowedWeakRanges,
                 BracketedStatement, ExpectOperandAccepted);
  ForEachOperand(kOperandDeclarationPlaces, {"always"}, kAllowedWeakRanges,
                 BracketedDeclaration, ExpectOperandAccepted);
}

TEST(AlwaysRangeElaboration,
     DISABLED_ABadStrongRangeIsReportedInEveryDirective) {
  for (const char* range : {"3:1", "-1:2", "2:$"}) {
    for (const std::string& target :
         OperandDirectives(std::string("s_always [") + range + "] a")) {
      SCOPED_TRACE(target);
      ExpectOperandReported(
          OperandIn("module", target),
          std::string(range) == "2:$" ? kBoundedReport : kRangeReport,
          "16.12.11");
    }
  }
}

TEST(AlwaysRangeElaboration, AGoodRangeIsAcceptedInEveryDirective) {
  for (const char* spec : {"s_always [1:2] a", "always [1:$] a", "always a"}) {
    for (const std::string& target : OperandDirectives(spec)) {
      SCOPED_TRACE(target);
      ExpectOperandAccepted(OperandIn("module", target));
    }
  }
}

TEST(AlwaysRangeElaboration,
     DISABLED_ABadActualForAFormalStrongRangeIsReported) {
  for (const char* actuals :
       {"-1, 2", "0, -1", "3, 1", "NEG, 2", "LO, HI", "k, 2", "0, k", "1.5, 2",
        "R, 3", "1, R", "S, 3"}) {
    SCOPED_TRACE(actuals);
    ExpectOperandReported(
        FormalOperandSource("lo, hi", "s_always [lo:hi]", actuals),
        kRangeReport, "16.12.11", kOperandLine + 1);
  }
}

TEST(AlwaysRangeElaboration, AGoodActualForAFormalRangeIsAccepted) {
  for (const char* actuals : {"0, 2", "3, 3", "ONE, HI", "int'(R), 2"}) {
    for (const char* op : {"s_always", "always"}) {
      SCOPED_TRACE(std::string(op) + " " + actuals);
      ExpectOperandAccepted(
          FormalOperandSource("lo, hi", std::string(op) + " [lo:hi]", actuals));
    }
  }
}

TEST(AlwaysRangeElaboration,
     DISABLED_ADollarActualForAFormalWeakMaximumIsAccepted) {
  ExpectOperandAccepted(
      FormalOperandSource("lo, hi", "always [lo:hi]", "1, $"));
}

TEST(AlwaysRangeElaboration,
     DISABLED_AStrongAlwaysWithoutARangeIsReportedInEachPlace) {
  ExpectInEachPlace("s_always a", ExpectGrammarReported);
}

TEST(AlwaysRangeElaboration, AWeakAlwaysWithoutARangeIsAcceptedInEachPlace) {
  ExpectInEachPlace("always a", ExpectOperandAccepted);
}

}  // namespace
