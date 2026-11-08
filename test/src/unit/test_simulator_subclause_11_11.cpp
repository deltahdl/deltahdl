#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

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
