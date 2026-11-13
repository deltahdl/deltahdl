#include <gtest/gtest.h>

#include <string>

#include "elaborator/nexttime_index.h"
#include "fixture_elaborator.h"
#include "helpers_bracketed_operand_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NexttimeIndex, NonNegativeConstantIsWellFormed) {
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(0)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(1)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(7)));
}

TEST(NexttimeIndex, NegativeConstantIsRejected) {
  EXPECT_FALSE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(-1)));
}

TEST(NexttimeIndex, NonConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = false;
  index.is_integer = true;
  index.value = 2;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

TEST(NexttimeIndex, NonIntegerConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = true;
  index.is_integer = false;
  index.value = 0;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

TEST(NexttimeIndexElaboration, AParameterIndexIsChecked) {
  const char* const kReport =
      "the index of nexttime shall be a non-negative integer constant "
      "expression";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  int k;\n"
      "  localparam int NEG = -1, ONE = 1;\n"
      "  a1: assert property (@(posedge clk) nexttime [NEG] a);\n"
      "  a2: assert property (@(posedge clk) s_nexttime [k] a);\n"
      "  a3: assert property (@(posedge clk) nexttime [ONE] a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.12.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.12.10"));
}

constexpr const char* kIndexReport = "non-negative integer constant";

constexpr const char* kForbiddenIndices[] = {"-1",  "(-1)", "NEG", "k",
                                             "1.5", "R",    "S"};

constexpr const char* kAllowedIndices[] = {"0",       "1",         "ONE",
                                           "int'(R)", "$clog2(4)", "(2)"};

void ExpectIndexReported(const std::string& src) {
  ExpectOperandReported(src, kIndexReport, "16.12.10");
}

TEST(NexttimeIndexElaboration,
     DISABLED_ABadIndexInAnAssertionStatementIsReportedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"nexttime", "s_nexttime"},
                 kForbiddenIndices, BracketedStatement, ExpectIndexReported);
}

TEST(NexttimeIndexElaboration,
     DISABLED_ABadIndexInAPropertyDeclarationIsReportedInEachPlace) {
  ForEachOperand(kOperandDeclarationPlaces, {"nexttime", "s_nexttime"},
                 kForbiddenIndices, BracketedDeclaration, ExpectIndexReported);
}

TEST(NexttimeIndexElaboration, AGoodIndexIsAcceptedInEachPlace) {
  ForEachOperand(kOperandStatementPlaces, {"nexttime", "s_nexttime"},
                 kAllowedIndices, BracketedStatement, ExpectOperandAccepted);
  ForEachOperand(kOperandDeclarationPlaces, {"nexttime", "s_nexttime"},
                 kAllowedIndices, BracketedDeclaration, ExpectOperandAccepted);
}

TEST(NexttimeIndexElaboration,
     DISABLED_ANegativeLiteralIndexIsReportedInEveryDirective) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    for (const char* index : {"-1", "(-1)"}) {
      for (const std::string& target :
           OperandDirectives(std::string(op) + " [" + index + "] a")) {
        SCOPED_TRACE(target);
        ExpectIndexReported(OperandIn("module", target));
      }
    }
  }
}

TEST(NexttimeIndexElaboration, AGoodIndexIsAcceptedInEveryDirective) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    for (const std::string& target :
         OperandDirectives(std::string(op) + " [1] a")) {
      SCOPED_TRACE(target);
      ExpectOperandAccepted(OperandIn("module", target));
    }
  }
}

TEST(NexttimeIndexElaboration, DISABLED_ABadActualForAFormalIndexIsReported) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    for (const char* actual : {"-1", "NEG", "k", "1.5", "R", "S"}) {
      SCOPED_TRACE(std::string(op) + " " + actual);
      ExpectOperandReported(
          FormalOperandSource("n", std::string(op) + " [n]", actual),
          kIndexReport, "16.12.10", kOperandLine + 1);
    }
  }
}

TEST(NexttimeIndexElaboration, AGoodActualForAFormalIndexIsAccepted) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    for (const char* actual : {"0", "1", "ONE", "int'(R)"}) {
      SCOPED_TRACE(std::string(op) + " " + actual);
      ExpectOperandAccepted(
          FormalOperandSource("n", std::string(op) + " [n]", actual));
    }
  }
}

}  // namespace
