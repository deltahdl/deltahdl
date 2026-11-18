#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(GateDelaySimulator, ProductionUndecoratedGateLeavesSchedulerAtInputTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and g(y, a, a);\n"
      "  initial begin a = 1'b0; #4 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 4u);
}

TEST(GateDelaySimulator, GateWithDelaySpecifiesPropagationDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #3 g(y, a, a);\n"
      "  initial begin a = 1'b0; #4 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

struct StepCase {
  std::string instance;
  std::string start;
  std::string change;
  std::string expected;
};

std::string ShownAtTheChangeAndAStepLater(const StepCase& c) {
  SimFixture f;
  return RunCapture(
      "module top;\n"
      "  logic a, c, n, p;\n"
      "  wire y, w;\n"
      "  wire x = 1'b1;\n"
      "  " +
          c.instance +
          ";\n"
          "  initial begin\n"
          "    " +
          c.start +
          "\n"
          "    #5 " +
          c.change +
          " $strobe(\"%b%b\", y, w);\n"
          "    #1 $display(\"%b%b\", y, w);\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(GateDelaySimulator, AnUndelayedGateOrSwitchChangesInTheSameStep) {
  const StepCase kCases[] = {
      {"nand g(y, a, c)", "a = 0; c = 1;", "a = 1;", "0z\n0z\n"},
      {"or g(y, a, c)", "a = 0; c = 0;", "a = 1;", "1z\n1z\n"},
      {"nor g(y, a, c)", "a = 0; c = 0;", "a = 1;", "0z\n0z\n"},
      {"xor g(y, a, c)", "a = 0; c = 0;", "a = 1;", "1z\n1z\n"},
      {"xnor g(y, a, c)", "a = 0; c = 0;", "a = 1;", "0z\n0z\n"},
      {"not g(y, a)", "a = 0;", "a = 1;", "0z\n0z\n"},
      {"bufif0 g(y, a, c)", "a = 0; c = 0;", "a = 1;", "1z\n1z\n"},
      {"notif0 g(y, a, c)", "a = 0; c = 0;", "a = 1;", "0z\n0z\n"},
      {"notif1 g(y, a, c)", "a = 0; c = 1;", "a = 1;", "0z\n0z\n"},
      {"nmos g(y, a, c)", "a = 0; c = 1;", "a = 1;", "1z\n1z\n"},
      {"pmos g(y, a, c)", "a = 0; c = 0;", "a = 1;", "1z\n1z\n"},
      {"rnmos g(y, a, c)", "a = 0; c = 1;", "a = 1;", "1z\n1z\n"},
      {"rpmos g(y, a, c)", "a = 0; c = 0;", "a = 1;", "1z\n1z\n"},
      {"rcmos g(y, a, n, p)", "a = 0; n = 1; p = 0;", "a = 1;", "1z\n1z\n"},
      {"cmos g(y, a, n, p)", "a = 1; n = 1; p = 0;", "n = 0; p = 1;",
       "zz\nzz\n"},
      {"tranif1 g(x, w, c)", "c = 0;", "c = 1;", "z1\nz1\n"},
      {"tranif0 g(x, w, c)", "c = 1;", "c = 0;", "z1\nz1\n"},
      {"rtranif1 g(x, w, c)", "c = 0;", "c = 1;", "z1\nz1\n"},
      {"rtranif0 g(x, w, c)", "c = 1;", "c = 0;", "z1\nz1\n"}};
  for (const StepCase& c : kCases) {
    EXPECT_EQ(ShownAtTheChangeAndAStepLater(c), c.expected) << c.instance;
  }
}

TEST(GateDelaySimulator, ADelayedSwitchChangesOnlyAfterItsDelay) {
  const StepCase kCases[] = {
      {"nmos #1 g(y, a, c)", "a = 0; c = 1;", "a = 1;", "0z\n1z\n"},
      {"pmos #1 g(y, a, c)", "a = 0; c = 0;", "a = 1;", "0z\n1z\n"},
      {"tranif1 #1 g(x, w, c)", "c = 0;", "c = 1;", "zz\nz1\n"},
      {"tranif0 #1 g(x, w, c)", "c = 1;", "c = 0;", "zz\nz1\n"},
      {"rtranif1 #1 g(x, w, c)", "c = 0;", "c = 1;", "zz\nz1\n"},
      {"rtranif0 #1 g(x, w, c)", "c = 1;", "c = 0;", "zz\nz1\n"}};
  for (const StepCase& c : kCases) {
    EXPECT_EQ(ShownAtTheChangeAndAStepLater(c), c.expected) << c.instance;
  }
}

}  // namespace
