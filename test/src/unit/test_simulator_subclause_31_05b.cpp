#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kSetupViolation = "$setup violation: data signal";
constexpr const char* kHoldViolation = "$hold violation: data signal";

bool RanCheck(const std::string& check, const char* initial_clk,
              const char* stimulus, SimFixture& f) {
  std::string src =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    " +
      check +
      "\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = " +
      initial_clk + ";\n" + stimulus +
      "  end\n"
      "endmodule\n";
  auto* rtl = ElaborateSrc(src, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

void ExpectClockTransitionAnswers(const char* event, const char* from,
                                  const char* to, bool answers) {
  SimFixture f;
  std::string check = "$setup(d, ";
  check += event;
  check += " clk, 5);";
  std::string stimulus = "    #10 d = 1'b1;\n    #2 clk = ";
  stimulus += to;
  stimulus += ";\n";
  ASSERT_TRUE(RanCheck(check, from, stimulus.c_str(), f)) << check;
  if (answers) {
    EXPECT_TRUE(
        ReportedWarning(f.diag.Diagnostics(), kSetupViolation, 5, "31.3.1"))
        << event << " " << from << " -> " << to;
  } else {
    EXPECT_EQ(FindDiag(f, kSetupViolation), nullptr)
        << event << " " << from << " -> " << to;
  }
}

TEST(EdgeControlSpecifierEvaluation, NegedgeAnswersEachTransitionOfItsList) {
  ExpectClockTransitionAnswers("negedge", "1'b1", "1'b0", true);
  ExpectClockTransitionAnswers("negedge", "1'bx", "1'b0", true);
  ExpectClockTransitionAnswers("negedge", "1'b1", "1'bx", true);
}

TEST(EdgeControlSpecifierEvaluation, NegedgeIgnoresEachRisingTransition) {
  ExpectClockTransitionAnswers("negedge", "1'b0", "1'b1", false);
  ExpectClockTransitionAnswers("negedge", "1'b0", "1'bx", false);
  ExpectClockTransitionAnswers("negedge", "1'bx", "1'b1", false);
}

TEST(EdgeControlSpecifierEvaluation, PosedgeAnswersTheTransitionsThroughX) {
  ExpectClockTransitionAnswers("posedge", "1'b0", "1'bx", true);
  ExpectClockTransitionAnswers("posedge", "1'bx", "1'b1", true);
}

TEST(EdgeControlSpecifierEvaluation, PosedgeIgnoresEachFallingTransition) {
  ExpectClockTransitionAnswers("posedge", "1'b1", "1'b0", false);
  ExpectClockTransitionAnswers("posedge", "1'b1", "1'bx", false);
  ExpectClockTransitionAnswers("posedge", "1'bx", "1'b0", false);
}

TEST(EdgeControlSpecifierEvaluation, ZDescriptorsAnswerTheMatchingXTransition) {
  ExpectClockTransitionAnswers("edge[0z]", "1'b0", "1'bx", true);
  ExpectClockTransitionAnswers("edge[z0]", "1'bx", "1'b0", true);
  ExpectClockTransitionAnswers("edge[0z]", "1'b0", "1'b1", false);
  ExpectClockTransitionAnswers("edge[z0]", "1'b1", "1'b0", false);
}

TEST(EdgeControlSpecifierEvaluation, ZLevelTransitionsAnswerTheirXDescriptor) {
  ExpectClockTransitionAnswers("edge[0x]", "1'b0", "1'bz", true);
  ExpectClockTransitionAnswers("edge[01]", "1'b0", "1'bz", false);
  ExpectClockTransitionAnswers("edge[x0]", "1'bz", "1'b0", true);
  ExpectClockTransitionAnswers("edge[x1]", "1'bz", "1'b1", true);
  ExpectClockTransitionAnswers("edge[10]", "1'bz", "1'b0", false);
}

TEST(EdgeControlSpecifierEvaluation, PosedgeAndNegedgeAnswerZTransitions) {
  ExpectClockTransitionAnswers("posedge", "1'b0", "1'bz", true);
  ExpectClockTransitionAnswers("posedge", "1'bz", "1'b1", true);
  ExpectClockTransitionAnswers("negedge", "1'b1", "1'bz", true);
  ExpectClockTransitionAnswers("negedge", "1'bz", "1'b0", true);
  ExpectClockTransitionAnswers("posedge", "1'b1", "1'bz", false);
  ExpectClockTransitionAnswers("negedge", "1'b0", "1'bz", false);
}

TEST(EdgeControlSpecifierEvaluation, XToZAndZToXAnswerNoDescriptor) {
  ExpectClockTransitionAnswers("edge[01, 10, 0x, x0, 1x, x1]", "1'bx", "1'bz",
                               false);
  ExpectClockTransitionAnswers("edge[01, 10, 0x, x0, 1x, x1]", "1'bz", "1'bx",
                               false);
}

TEST(EdgeControlSpecifierEvaluation, Edge1xAndX0AnswerTheirTransitions) {
  ExpectClockTransitionAnswers("edge[1x]", "1'b1", "1'bx", true);
  ExpectClockTransitionAnswers("edge[x0]", "1'bx", "1'b0", true);
  ExpectClockTransitionAnswers("edge[x0]", "1'bx", "1'b1", false);
}

TEST(EdgeControlSpecifierEvaluation, DataEventDescriptorAnswersARise) {
  SimFixture f;
  ASSERT_TRUE(RanCheck("$hold(posedge clk, edge[01] d, 10);", "1'b0",
                       "    #10 clk = 1'b1;\n"
                       "    #3 d = 1'b1;\n",
                       f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), kHoldViolation, 5, "31.3.2"));
}

TEST(EdgeControlSpecifierEvaluation, DataEventDescriptorIgnoresAFall) {
  SimFixture f;
  ASSERT_TRUE(RanCheck("$hold(posedge clk, edge[01] d, 10);", "1'b0",
                       "    #5 d = 1'b1;\n"
                       "    #5 clk = 1'b1;\n"
                       "    #3 d = 1'b0;\n",
                       f));
  EXPECT_EQ(FindDiag(f, kHoldViolation), nullptr);
}

}  // namespace
