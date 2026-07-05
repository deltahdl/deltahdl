#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// Elaborate and run a single-module source under the given delay mode,
// capturing everything the run writes to stdout. The min:typ:max expression
// under test is built from real source syntax and driven through the full
// pipeline; only the mode selection (an environment setting, not part of the
// expression's syntax) is applied through the fixture.
std::string RunCapture(const std::string& src, SimFixture& f, DelayMode mode) {
  f.ctx.SetDelayMode(mode);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §11.11: the three colon-separated values represent minimum, typical, and
// maximum — in that order. A single triplet used as an expression selects the
// matching member for the active delay mode.
TEST(MinTypMaxSim, SelectsMemberByModeInOrder) {
  const char* src =
      "module t;\n"
      "  int r;\n"
      "  initial begin r = (10:20:30); $display(\"%0d\", r); end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "10\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kTyp), "20\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "30\n");
  }
}

// §11.11 Example 1: two triplets combined by a binary operator. The operator
// sees the per-mode member of each operand — min: 1+4, typ: 2+5, max: 3+6.
TEST(MinTypMaxSim, TwoTripletsCombined) {
  const char* src =
      "module t;\n"
      "  int r;\n"
      "  initial begin r = (1:2:3) + (4:5:6); $display(\"%0d\", r); end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "5\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kTyp), "7\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "9\n");
  }
}

// §11.11 Example 2: a triplet mixed with a plain operand. The plain operand is
// mode-independent; only the triplet contributes the selected member.
TEST(MinTypMaxSim, TripletMixedWithPlainOperand) {
  const char* src =
      "module t;\n"
      "  int r;\n"
      "  initial begin r = 200 - (50:75:100); $display(\"%0d\", r); end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "150\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kTyp), "125\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "100\n");
  }
}

// §11.11 constant_mintypmax_expression: each member may itself be a constant
// expression. Here the three members are localparams (a §11.2.1 constant form),
// built from real source and driven through the full pipeline; the active mode
// still selects the matching member, confirming the triplet accepts
// constant-form operands rather than only literals.
TEST(MinTypMaxSim, MembersFromLocalparamConstants) {
  const char* src =
      "module t;\n"
      "  localparam int A = 10;\n"
      "  localparam int B = 20;\n"
      "  localparam int C = 30;\n"
      "  int r;\n"
      "  initial begin r = (A:B:C); $display(\"%0d\", r); end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "10\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kTyp), "20\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "30\n");
  }
}

// §11.11 constant_mintypmax_expression, parameter form: a module parameter is a
// §11.2.1 constant that resolves along a different path than a localparam, so
// it is exercised separately. Built from real source and driven end to end, the
// active mode still selects the matching member.
TEST(MinTypMaxSim, MembersFromParameterConstants) {
  const char* src =
      "module t;\n"
      "  parameter int A = 10;\n"
      "  parameter int B = 20;\n"
      "  parameter int C = 30;\n"
      "  int r;\n"
      "  initial begin r = (A:B:C); $display(\"%0d\", r); end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "10\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kTyp), "20\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "30\n");
  }
}

// §11.11 "used wherever expressions can appear": the triplet members may be
// arbitrary (non-constant) expressions, not just constants. Here they are
// runtime variables assigned before the triplet is read; the selected member
// still follows the active mode, confirming member evaluation runs at
// simulation time over real variable values.
TEST(MinTypMaxSim, MembersFromRuntimeVariables) {
  const char* src =
      "module t;\n"
      "  int a, b, c, r;\n"
      "  initial begin\n"
      "    a = 10; b = 20; c = 30;\n"
      "    r = (a:b:c);\n"
      "    $display(\"%0d\", r);\n"
      "  end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "10\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kTyp), "20\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "30\n");
  }
}

// §11.11's headline syntactic position: a min:typ:max triplet used as a
// procedural delay control. The selected member becomes the delay amount, so
// the simulation time reached after the delay reflects the active mode. Built
// from real source and driven end to end; time is observed via $time.
TEST(MinTypMaxSim, TripletAsProceduralDelay) {
  const char* src =
      "module t;\n"
      "  initial begin\n"
      "    #(10:20:30);\n"
      "    if ($time == 10) $display(\"min\");\n"
      "    if ($time == 20) $display(\"typ\");\n"
      "    if ($time == 30) $display(\"max\");\n"
      "  end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "min\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kTyp), "typ\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "max\n");
  }
}

// mintypmax_expression's first alternative is a plain expression: a
// parenthesized single value yields that value regardless of delay mode.
TEST(MinTypMaxSim, SingleValueIsModeIndependent) {
  const char* src =
      "module t;\n"
      "  int r;\n"
      "  initial begin r = (42); $display(\"%0d\", r); end\n"
      "endmodule\n";
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMin), "42\n");
  }
  {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f, DelayMode::kMax), "42\n");
  }
}

}  // namespace
