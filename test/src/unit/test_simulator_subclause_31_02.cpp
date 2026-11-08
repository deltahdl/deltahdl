#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "parser/ast_specify.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

const SpecifyManager* SpecifyStateAfterRun(const std::string& source,
                                           SimFixture& f) {
  auto* design = ElaborateSrc(source, f);
  if (design == nullptr || f.has_errors) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.GetSpecifyManager();
}

const TimingCheckEntry* RegisteredCheckOfKind(const SpecifyManager& mgr,
                                              TimingCheckKind kind) {
  for (const auto& check : mgr.GetTimingChecks()) {
    if (check.kind == kind) return &check;
  }
  return nullptr;
}

const TimingCheckEntry* RegisteredCheckIn(const SpecifyManager& mgr,
                                          std::string_view prefix) {
  for (const auto& check : mgr.GetTimingChecks()) {
    if (check.inst_prefix == prefix) return &check;
  }
  return nullptr;
}

TEST(RegisteredDesignTimingChecks, DeclaredSetupCheckReachesTheManager) {
  SimFixture f;
  const SpecifyManager* mgr = SpecifyStateAfterRun(
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 7);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const TimingCheckEntry* check =
      RegisteredCheckOfKind(*mgr, TimingCheckKind::kSetup);
  ASSERT_NE(check, nullptr);
  EXPECT_EQ(check->ref_signal, "clk");
  EXPECT_EQ(check->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(check->data_signal, "d");
  EXPECT_EQ(check->limit, 7u);
}

TEST(RegisteredDesignTimingChecks,
     TwoInstancesOfOneCellRegisterTheirOwnChecks) {
  SimFixture f;
  const SpecifyManager* mgr = SpecifyStateAfterRun(
      "module setup_cell(input d, input clk, output q);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 19);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic first_q;\n"
      "  logic second_q;\n"
      "  setup_cell u_first(1'b0, 1'b0, first_q);\n"
      "  setup_cell u_second(1'b0, 1'b0, second_q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->TimingCheckCount(), 2u);
  const TimingCheckEntry* first = RegisteredCheckIn(*mgr, "u_first.");
  ASSERT_NE(first, nullptr);
  EXPECT_FALSE(first->data_signal.empty());
  const TimingCheckEntry* second = RegisteredCheckIn(*mgr, "u_second.");
  ASSERT_NE(second, nullptr);
  EXPECT_FALSE(second->data_signal.empty());
}

TEST(RegisteredDesignTimingChecks, SpecparamLimitIsReadInDeclaringInstance) {
  SimFixture f;
  const SpecifyManager* mgr = SpecifyStateAfterRun(
      "module limited_cell(input d, input clk, output q);\n"
      "  specify\n"
      "    specparam T = 29;\n"
      "    $setup(d, posedge clk, T);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic only_q;\n"
      "  limited_cell u_only(1'b0, 1'b0, only_q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const TimingCheckEntry* check = RegisteredCheckIn(*mgr, "u_only.");
  ASSERT_NE(check, nullptr);
  EXPECT_EQ(check->limit, 29u);
}

TEST(RegisteredDesignTimingChecks, InterfacePortMemberTerminalsFollowTheBus) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus;\n"
                       "  logic clk = 0, d = 0;\n"
                       "endinterface\n"
                       "module dut(bus b);\n"
                       "  reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $setup(b.d, posedge b.clk, 5, n);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus b();\n"
                       "  dut u(b);\n"
                       "  initial begin\n"
                       "    #10 b.d = 1; #2 b.clk = 1;\n"
                       "    #8 b.clk = 0;\n"
                       "    #10 b.d = 0; #6 b.clk = 1;\n"
                       "    #5 $display(\"%0d\", u.cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(RegisteredDesignTimingChecks,
     InterfacePortMemberTerminalsFollowTheInterfacesOwnDriver) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus;\n"
                       "  logic clk = 0, d = 0;\n"
                       "  initial begin\n"
                       "    #10 d = 1; #2 clk = 1;\n"
                       "    #8 clk = 0;\n"
                       "    #10 d = 0; #6 clk = 1;\n"
                       "  end\n"
                       "endinterface\n"
                       "module dut(bus b);\n"
                       "  reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $setup(b.d, posedge b.clk, 5, n);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus b();\n"
                       "  dut u(b);\n"
                       "  initial #41 $display(\"%0d\", u.cnt);\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(RegisteredDesignTimingChecks, SelectTerminalsFollowTheirBitsAlone) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module dut(input clk, input [3:0] d);\n"
                       "  reg n = 0, n2 = 0; integer cnt = 0, cnt2 = 0;\n"
                       "  specify\n"
                       "    $setup(d[1], posedge clk, 5, n);\n"
                       "    $setup(d[3:2], posedge clk, 5, n2);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  always @(n2) cnt2 = cnt2 + 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg clk = 0; reg [3:0] d = 0;\n"
                       "  dut u(.clk(clk), .d(d));\n"
                       "  initial begin\n"
                       "    #10 d[0] = 1; #2 clk = 1;\n"
                       "    #8 clk = 0;\n"
                       "    #10 d[1] = 1; #2 clk = 1;\n"
                       "    #8 clk = 0;\n"
                       "    #10 d[3] = 1; #2 clk = 1;\n"
                       "    #5 $display(\"%0d %0d\", u.cnt, u.cnt2);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1\n");
}

TEST(RegisteredDesignTimingChecks, BitSelectReferenceFollowsItsBit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module dutv(input [1:0] clk, input d);\n"
                       "  reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $setup(d, posedge clk[1], 5, n);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg [1:0] clk = 0, d = 0;\n"
                       "  dutv uv(.clk(clk), .d(d[0]));\n"
                       "  initial begin\n"
                       "    #10 d = 2'b11;\n"
                       "    #2 clk[0] = 1;\n"
                       "    #6 clk[1] = 1;\n"
                       "    #2 clk = 0; #5 d[0] = 0; #2 clk[1] = 1;\n"
                       "    #5 $display(\"%0d\", uv.cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(RegisteredDesignTimingChecks, ChecksOnTheSameSignalsAreEachEvaluated) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(output reg clk = 0, output reg d = 0);\n"
                       "  reg n1 = 0, n2 = 0, n3 = 0;\n"
                       "  specify\n"
                       "    $setup(d, posedge clk, 5, n1);\n"
                       "    $setup(d, posedge clk, 5, n2);\n"
                       "    $setup(d, posedge clk, 5, n3);\n"
                       "  endspecify\n"
                       "  initial begin\n"
                       "    #10 d = 1; #2 clk = 1;\n"
                       "    #5 $display(\"%b%b%b\", n1, n2, n3);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "111\n");
}

TEST(RegisteredDesignTimingChecks, ChecksOnTheSameSignalsKeepTheirLimits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(output reg c1 = 0, output reg c2 = 0);\n"
                       "  reg n5 = 0, n9 = 0;\n"
                       "  specify\n"
                       "    $skew(posedge c1, posedge c2, 5, n5);\n"
                       "    $skew(posedge c1, posedge c2, 9, n9);\n"
                       "  endspecify\n"
                       "  initial begin\n"
                       "    #10 c1 = 1; #7 c2 = 1;\n"
                       "    #1 $display(\"%b%b\", n5, n9);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "10\n");
}

TEST(RegisteredDesignTimingChecks, ChecksOnTheSameSignalsKeepTheirEdges) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(output reg clk = 0, output reg d = 0);\n"
                       "  reg n = 0, n2 = 0; integer cnt = 0, cnt2 = 0;\n"
                       "  specify\n"
                       "    $setup(d, edge[01] clk, 5, n);\n"
                       "    $setup(d, edge[10] clk, 5, n2);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  always @(n2) cnt2 = cnt2 + 1;\n"
                       "  initial begin\n"
                       "    #10 d = 1; #2 clk = 1;\n"
                       "    #8 d = 0; #2 clk = 0;\n"
                       "    #5 $display(\"%0d %0d\", cnt, cnt2);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1\n");
}

}  // namespace
