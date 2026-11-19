#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string NotifierAfterOneCheck(const char* check, const char* stimulus) {
  SimFixture f;
  std::string src =
      "module top(\n"
      "    output logic a,\n"
      "    output logic b);\n"
      "  reg n = 1'b0;\n"
      "  specify\n"
      "    ";
  src += check;
  src +=
      "\n"
      "  endspecify\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 1'b0;\n";
  src += stimulus;
  src +=
      "    #60 $display(\"%b\", n);\n"
      "  end\n"
      "endmodule\n";
  return RunCapture(src, f);
}

TEST(NotifierUpdateDriven, HoldViolationTogglesTheNotifier) {
  EXPECT_EQ(NotifierAfterOneCheck("$hold(posedge a, b, 10, n);",
                                  "    #10 a = 1'b1;\n"
                                  "    #3 b = 1'b1;\n"),
            "1\n");
}

TEST(NotifierUpdateDriven, RecoveryViolationTogglesTheNotifier) {
  EXPECT_EQ(NotifierAfterOneCheck("$recovery(posedge a, posedge b, 10, n);",
                                  "    #10 a = 1'b1;\n"
                                  "    #3 b = 1'b1;\n"),
            "1\n");
}

TEST(NotifierUpdateDriven, RemovalViolationTogglesTheNotifier) {
  EXPECT_EQ(NotifierAfterOneCheck("$removal(posedge a, posedge b, 10, n);",
                                  "    #10 b = 1'b1;\n"
                                  "    #3 a = 1'b1;\n"),
            "1\n");
}

TEST(NotifierUpdateDriven, RecremViolationTogglesTheNotifier) {
  EXPECT_EQ(NotifierAfterOneCheck("$recrem(posedge a, posedge b, 10, 10, n);",
                                  "    #10 a = 1'b1;\n"
                                  "    #3 b = 1'b1;\n"),
            "1\n");
}

TEST(NotifierUpdateDriven, TimeskewViolationTogglesTheNotifier) {
  EXPECT_EQ(NotifierAfterOneCheck("$timeskew(posedge a, posedge b, 10, n);",
                                  "    #10 a = 1'b1;\n"
                                  "    #15 b = 1'b1;\n"),
            "1\n");
}

TEST(NotifierUpdateDriven, FullskewViolationTogglesTheNotifier) {
  EXPECT_EQ(
      NotifierAfterOneCheck("$fullskew(posedge a, posedge b, 10, 20, n, 1, 0);",
                            "    #10 a = 1'b1;\n"
                            "    #15 b = 1'b1;\n"),
      "1\n");
}

TEST(NotifierUpdateDriven, PeriodViolationTogglesTheNotifier) {
  EXPECT_EQ(NotifierAfterOneCheck("$period(posedge a, 10, n);",
                                  "    #10 a = 1'b1;\n"
                                  "    #2 a = 1'b0;\n"
                                  "    #2 a = 1'b1;\n"),
            "1\n");
}

TEST(NotifierUpdateDriven, WidthViolationTogglesTheNotifier) {
  EXPECT_EQ(NotifierAfterOneCheck("$width(posedge a, 10, 0, n);",
                                  "    #10 a = 1'b1;\n"
                                  "    #3 a = 1'b0;\n"),
            "1\n");
}

TEST(NotifierUpdateDriven, SharedNotifierTogglesAtEachChecksViolation) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output logic a,\n"
                       "    output logic b);\n"
                       "  reg n = 1'b0;\n"
                       "  specify\n"
                       "    $setup(b, posedge a, 10, n);\n"
                       "    $hold(posedge a, b, 10, n);\n"
                       "  endspecify\n"
                       "  initial begin\n"
                       "    a = 1'b0;\n"
                       "    b = 1'b0;\n"
                       "    #5 b = 1'b1;\n"
                       "    #5 a = 1'b1;\n"
                       "    #1 $display(\"%b\", n);\n"
                       "    #2 b = 1'b0;\n"
                       "    #1 $display(\"%b\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n0\n");
}

TEST(NotifierUpdateDriven, EachInstanceTogglesOnlyItsOwnNotifier) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf(input a, input b);\n"
                       "  reg n = 1'b0;\n"
                       "  specify\n"
                       "    $hold(posedge a, b, 10, n);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a1 = 1'b0, b1 = 1'b0, a2 = 1'b0, b2 = 1'b0;\n"
                       "  leaf c1(a1, b1);\n"
                       "  leaf c2(a2, b2);\n"
                       "  initial begin\n"
                       "    #10 a1 = 1'b1; a2 = 1'b1;\n"
                       "    #3 b1 = 1'b1;\n"
                       "    #30 b2 = 1'b1;\n"
                       "    #5 $display(\"%b%b\", c1.n, c2.n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "10\n");
}

TEST(NotifierUpdateDriven, NotifierDeclaredAfterTheSpecifyBlockToggles) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output logic a,\n"
                       "    output logic b);\n"
                       "  specify\n"
                       "    $hold(posedge a, b, 10, late);\n"
                       "  endspecify\n"
                       "  reg late = 1'b0;\n"
                       "  initial begin\n"
                       "    a = 1'b0;\n"
                       "    b = 1'b0;\n"
                       "    #10 a = 1'b1;\n"
                       "    #3 b = 1'b1;\n"
                       "    #5 $display(\"%b\", late);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

}  // namespace
