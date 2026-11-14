#include <gtest/gtest.h>

#include <string>

#include "helpers_disable_iff_runs.h"
#include "helpers_report_times.h"

using namespace delta;

namespace {

constexpr const char* kPorts = "(input logic a, b, clk, rst, rst1);\n";

constexpr const char* kInstance = "  m1 u1(a, b, clk, rst, rst1);\n";

constexpr const char* kInner = "default disable iff rst;\n";

std::string RunModule(const std::string& body) {
  return RunDisableIffDesign(
      std::string("module m1") + kPorts + body + "endmodule\n", kInstance);
}

std::string RunUnderOuterDefault(const std::string& body) {
  return RunModule("  default disable iff rst1;\n" + body);
}

TEST(DisableIffOverrideRun, ANestedInterfaceOrProgramsOwnDefaultOverrides) {
  std::string out =
      RunUnderOuterDefault("  interface ni;\n    " + std::string(kInner) +
                           FailingAt("a_ni", "    ") +
                           "  endinterface\n"
                           "  program np;\n    " +
                           kInner + FailingAt("a_np", "    ") +
                           "  endprogram\n"
                           "  ni u_ni();\n"
                           "  np u_np();\n");
  EXPECT_EQ(ReportTimes(out, "a_ni"), "35");
  EXPECT_EQ(ReportTimes(out, "a_np"), "35");
}

TEST(DisableIffOverrideRun, AnElseLoopOrCaseGenerateBlocksOwnDefaultOverrides) {
  std::string out = RunUnderOuterDefault(
      "  if (0) begin : g0\n"
      "  end else begin : ge\n    " +
      std::string(kInner) + FailingAt("a_else", "    ") +
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : lg\n    " +
      kInner + FailingAt("a_loop", "    ") +
      "  end\n"
      "  case (1)\n"
      "    1: begin : cg\n      " +
      kInner + FailingAt("a_case", "      ") +
      "    end\n"
      "  endcase\n");
  EXPECT_EQ(ReportTimes(out, "a_else"), "35");
  EXPECT_EQ(ReportTimes(out, "a_loop"), "35");
  EXPECT_EQ(ReportTimes(out, "a_case"), "35");
}

TEST(DisableIffOverrideRun, AGenerateBlockNestedInADefaultedBlockOverrides) {
  std::string out = RunModule(
      "  if (1) begin : g\n"
      "    default disable iff rst1;\n"
      "    if (1) begin : gi\n      " +
      std::string(kInner) + FailingAt("a_if_in_if", "      ") +
      "    end\n"
      "    for (genvar i = 0; i < 1; i++) begin : gl\n      " +
      kInner + FailingAt("a_loop_in_if", "      ") +
      "    end\n"
      "  end\n"
      "  for (genvar j = 0; j < 1; j++) begin : l\n"
      "    default disable iff rst1;\n"
      "    case (1)\n"
      "      1: begin : c\n        " +
      kInner + FailingAt("a_case_in_loop", "        ") +
      "      end\n"
      "    endcase\n"
      "  end\n");
  EXPECT_EQ(ReportTimes(out, "a_if_in_if"), "35");
  EXPECT_EQ(ReportTimes(out, "a_loop_in_if"), "35");
  EXPECT_EQ(ReportTimes(out, "a_case_in_loop"), "35");
}

TEST(DisableIffOverrideRun,
     AGenerateBlockOverridesTheDefaultOfAnInterfaceOrProgram) {
  std::string out = RunDisableIffDesign(
      std::string("interface ifc(input logic a, b, clk, rst, rst1);\n"
                  "  default disable iff rst1;\n"
                  "  if (1) begin : g\n    ") +
          kInner + FailingAt("a_ifc_g", "    ") +
          "  end\n"
          "endinterface\n"
          "program prg(input logic a, b, clk, rst, rst1);\n"
          "  default disable iff rst1;\n"
          "  if (1) begin : g\n    " +
          kInner + FailingAt("a_prg_g", "    ") +
          "  end\n"
          "endprogram\n",
      "  ifc u_ifc(a, b, clk, rst, rst1);\n"
      "  prg u_prg(a, b, clk, rst, rst1);\n");
  EXPECT_EQ(ReportTimes(out, "a_ifc_g"), "35");
  EXPECT_EQ(ReportTimes(out, "a_prg_g"), "35");
}

TEST(DisableIffOverrideRun, AnInterfaceNestedInADefaultedInterfaceOverrides) {
  std::string out = RunDisableIffDesign(
      std::string("interface ifc(input logic a, b, clk, rst, rst1);\n"
                  "  default disable iff rst1;\n"
                  "  interface ni;\n    ") +
          kInner + FailingAt("a_ni", "    ") +
          "  endinterface\n"
          "  ni u_ni();\n"
          "endinterface\n",
      "  ifc u_ifc(a, b, clk, rst, rst1);\n");
  EXPECT_EQ(ReportTimes(out, "a_ni"), "35");
}

TEST(DisableIffOverrideRun, TheInnermostOfThreeDefaultsWins) {
  std::string out = RunModule(
      "  default disable iff 1'b1;\n"
      "  module m2;\n"
      "    default disable iff rst1;\n"
      "    if (1) begin : g\n      " +
      std::string(kInner) + FailingAt("a_m2_g", "      ") +
      "    end\n"
      "  endmodule\n"
      "  interface ni;\n"
      "    default disable iff rst1;\n"
      "    if (1) begin : g\n      " +
      kInner + FailingAt("a_ni_g", "      ") +
      "    end\n"
      "  endinterface\n"
      "  program np;\n"
      "    default disable iff rst1;\n"
      "    if (1) begin : g\n      " +
      kInner + FailingAt("a_np_g", "      ") +
      "    end\n"
      "  endprogram\n"
      "  ni u_ni();\n"
      "  np u_np();\n");
  EXPECT_EQ(ReportTimes(out, "a_m2_g"), "35");
  EXPECT_EQ(ReportTimes(out, "a_ni_g"), "35");
  EXPECT_EQ(ReportTimes(out, "a_np_g"), "35");
}

TEST(DisableIffOverrideRun, AProcedureInsideAnOverridingScopeTakesTheInner) {
  std::string out = RunUnderOuterDefault(
      "  if (1) begin : g\n    " + std::string(kInner) +
      "    always @(posedge clk) a_gp: assert property (a |=> b) "
      "else $display(\"a_gp at %0d\", $time);\n"
      "  end\n"
      "  module m2;\n    " +
      kInner +
      "    always @(posedge clk) a_mp: assert property (a |=> b) "
      "else $display(\"a_mp at %0d\", $time);\n"
      "  endmodule\n");
  EXPECT_EQ(ReportTimes(out, "a_gp"), "35");
  EXPECT_EQ(ReportTimes(out, "a_mp"), "35");
}

}  // namespace
