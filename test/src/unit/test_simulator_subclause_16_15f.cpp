#include <gtest/gtest.h>

#include <string>

#include "helpers_disable_iff_runs.h"
#include "helpers_report_times.h"

using namespace delta;

namespace {

constexpr const char* kPorts = "(input logic a, b, clk, rst, rst1);\n";

constexpr const char* kInstance = "  m1 u1(a, b, clk, rst, rst1);\n";

std::string RunModule(const std::string& body) {
  return RunDisableIffDesign(
      std::string("module m1") + kPorts + body + "endmodule\n", kInstance);
}

TEST(DisableIffPositionRun, AnInterfaceProgramOrCheckerAssertionPrecedesIt) {
  std::string out = RunDisableIffDesign(
      "interface ifc(input logic a, b, clk, rst1);\n" + FailingAt("a_ifc") +
          "  default disable iff rst1;\n"
          "endinterface\n"
          "program prg(input logic a, b, clk, rst1);\n" +
          FailingAt("a_prg") +
          "  default disable iff rst1;\n"
          "endprogram\n"
          "checker chk(logic a, b, clk, rst1);\n" +
          FailingAt("a_chk") +
          "  default disable iff rst1;\n"
          "endchecker\n",
      "  ifc u_ifc(a, b, clk, rst1);\n"
      "  prg u_prg(a, b, clk, rst1);\n"
      "  chk u_chk(a, b, clk, rst1);\n");
  EXPECT_EQ(ReportTimes(out, "a_ifc"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_prg"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_chk"), "15 25");
}

TEST(DisableIffPositionRun, AGenerateBlocksAssertionPrecedesItsOwnDefault) {
  std::string out = RunModule(
      "  default disable iff rst;\n"
      "  if (1) begin : g\n" +
      FailingAt("a_if", "    ") +
      "    default disable iff rst1;\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : lg\n" +
      FailingAt("a_loop", "    ") +
      "    default disable iff rst1;\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : cg\n" +
      FailingAt("a_case", "      ") +
      "      default disable iff rst1;\n"
      "    end\n"
      "  endcase\n");
  EXPECT_EQ(ReportTimes(out, "a_if"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_loop"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_case"), "15 25");
}

TEST(DisableIffPositionRun, NestedScopesWrittenBeforeTheDefaultInherit) {
  std::string out = RunModule("  module m2;\n" + FailingAt("a_m2", "    ") +
                              "  endmodule\n"
                              "  interface ni;\n" +
                              FailingAt("a_ni", "    ") +
                              "  endinterface\n"
                              "  program np;\n" +
                              FailingAt("a_np", "    ") +
                              "  endprogram\n"
                              "  ni u_ni();\n"
                              "  np u_np();\n"
                              "  if (1) begin : g\n" +
                              FailingAt("a_g", "    ") +
                              "  end\n"
                              "  default disable iff rst1;\n");
  EXPECT_EQ(ReportTimes(out, "a_m2"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_ni"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_np"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_g"), "15 25");
}

TEST(DisableIffPositionRun, ProceduralAssumeAndCoverStatementsPrecedeIt) {
  std::string out = RunModule(
      "  always @(posedge clk) a_p: assert property (a |=> b) "
      "else $display(\"a_p at %0d\", $time);\n"
      "  u_m: assume property (@(posedge clk) a |=> b) "
      "else $display(\"u_m at %0d\", $time);\n"
      "  c_p: cover property (@(posedge clk) a ##1 !b) "
      "$display(\"c_p at %0d\", $time);\n"
      "  default disable iff rst1;\n");
  EXPECT_EQ(ReportTimes(out, "a_p"), "15 25");
  EXPECT_EQ(ReportTimes(out, "u_m"), "15 25");
  EXPECT_EQ(ReportTimes(out, "c_p"), "15 25");
}

}  // namespace
