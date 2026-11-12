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

TEST(MinTypMaxSim,
     TheExamplesAndEveryPlaceAnExpressionStandsTakeTheTypicalValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  int a = 1, b = 2, c = 3, d = 10, e = 20, f = 30, val = 200, r;\n"
          "  localparam int P = (4:5:6);\n"
          "  parameter int Q = (7:8:9) + 1;\n"
          "  logic x = 0;\n"
          "  wire #(1:2:3) y = x;\n"
          "  wire z;\n"
          "  assign #(4:5:6) z = x;\n"
          "  function int g(int v); return v; endfunction\n"
          "  logic [(1:3:5):0] w;\n"
          "  initial begin\n"
          "    r = (a:b:c) + (d:e:f); $write(\"%0d \", r);\n"
          "    r = val - (32'd 50: 32'd 75: 32'd 100); $write(\"%0d \", r);\n"
          "    $write(\"%0d %0d %0d %0d \", P, Q, g((1:2:3)), $bits(w));\n"
          "    x = 1;\n"
          "    #1 $write(\"%b%b \", y, z);\n"
          "    #1 $write(\"%b%b \", y, z);\n"
          "    #3 $write(\"%b%b %0t \", y, z, $time);\n"
          "    #(1:2:3) $display(\"%0t\", $time);\n"
          "  end\n"
          "endmodule\n",
          f),
      "22 125 5 9 2 4 xx 1x 11 5 7\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
