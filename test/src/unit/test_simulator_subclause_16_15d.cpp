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

std::string RunUnderOuterDefault(const std::string& body) {
  return RunModule("  default disable iff rst1;\n" + body);
}

TEST(DisableIffReachRun, ANestedInterfaceOrProgramDeclarationInherits) {
  std::string out =
      RunUnderOuterDefault("  interface ni;\n" + FailingAt("a_ni", "    ") +
                           "  endinterface\n"
                           "  program np;\n" +
                           FailingAt("a_np", "    ") +
                           "  endprogram\n"
                           "  ni u_ni();\n"
                           "  np u_np();\n");
  EXPECT_EQ(ReportTimes(out, "a_ni"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_np"), "15 25");
}

TEST(DisableIffReachRun, AModuleTwoDeclarationsDownInherits) {
  std::string out = RunUnderOuterDefault(
      "  module m2;\n"
      "    module m3;\n" +
      FailingAt("a_m3", "      ") +
      "    endmodule\n"
      "  endmodule\n");
  EXPECT_EQ(ReportTimes(out, "a_m3"), "15 25");
}

TEST(DisableIffReachRun, AGenerateBlockInANestedDeclarationInherits) {
  std::string out = RunUnderOuterDefault(
      "  module m2;\n"
      "    if (1) begin : gm\n" +
      FailingAt("a_gm", "      ") +
      "    end\n"
      "  endmodule\n"
      "  interface ni;\n"
      "    if (1) begin : gi\n" +
      FailingAt("a_gi", "      ") +
      "    end\n"
      "  endinterface\n"
      "  ni u_ni();\n");
  EXPECT_EQ(ReportTimes(out, "a_gm"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_gi"), "15 25");
}

TEST(DisableIffReachRun, EachKindOfGenerateBlockInherits) {
  std::string out = RunUnderOuterDefault(
      "  if (1) begin : g\n" + FailingAt("a_if", "    ") +
      "    for (genvar i = 0; i < 1; i++) begin : inner\n" +
      FailingAt("a_nested", "      ") +
      "    end\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : cg\n" +
      FailingAt("a_case", "      ") +
      "    end\n"
      "  endcase\n"
      "  for (genvar i = 0; i < 1; i++) begin : lg\n" +
      FailingAt("a_loop", "    ") + "  end\n");
  EXPECT_EQ(ReportTimes(out, "a_if"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_nested"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_case"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_loop"), "15 25");
}

TEST(DisableIffReachRun, AProceduralAssertionInANamedBlockInherits) {
  std::string out = RunUnderOuterDefault(
      "  always @(posedge clk) begin : blk\n"
      "    a_blk: assert property (a |=> b) "
      "else $display(\"a_blk at %0d\", $time);\n"
      "  end\n");
  EXPECT_EQ(ReportTimes(out, "a_blk"), "15 25");
}

TEST(DisableIffReachRun, AnAssertionInAnInitialProcedureInherits) {
  std::string out = RunUnderOuterDefault(
      "  initial begin : ib\n"
      "    #22;\n"
      "    a_inf: assert property (@(posedge clk) a |=> b) "
      "else $display(\"a_inf at %0d\", $time);\n"
      "    a_own: assert property (@(posedge clk) disable iff (1'b0) a |=> b) "
      "else $display(\"a_own at %0d\", $time);\n"
      "  end\n");
  EXPECT_EQ(ReportTimes(out, "a_inf"), "");
  EXPECT_EQ(ReportTimes(out, "a_own"), "35");
}

TEST(DisableIffReachRun, AnAssumeACoverPropertyAndACoverSequenceInherit) {
  std::string out = RunUnderOuterDefault(
      "  u_m: assume property (@(posedge clk) a |=> b) "
      "else $display(\"u_m at %0d\", $time);\n"
      "  c_p: cover property (@(posedge clk) a ##1 !b) "
      "$display(\"c_p at %0d\", $time);\n"
      "  c_s: cover sequence (@(posedge clk) a ##1 !b) "
      "$display(\"c_s at %0d\", $time);\n");
  EXPECT_EQ(ReportTimes(out, "u_m"), "15 25");
  EXPECT_EQ(ReportTimes(out, "c_p"), "15 25");
  EXPECT_EQ(ReportTimes(out, "c_s"), "15 25");
}

TEST(DisableIffReachRun, AnInterfacesOrProgramsDefaultGovernsItsAssertions) {
  std::string out = RunDisableIffDesign(
      "interface ifc(input logic a, b, clk, rst1);\n"
      "  default disable iff rst1;\n" +
          FailingAt("a_ifc") +
          "endinterface\n"
          "program prg(input logic a, b, clk, rst1);\n"
          "  default disable iff rst1;\n" +
          FailingAt("a_prg") + "endprogram\n",
      "  ifc u_ifc(a, b, clk, rst1);\n"
      "  prg u_prg(a, b, clk, rst1);\n");
  EXPECT_EQ(ReportTimes(out, "a_ifc"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_prg"), "15 25");
}

TEST(DisableIffReachRun, AGenerateBlocksDefaultReachesOnlyTheBlockAndItsNest) {
  std::string out = RunModule(
      "  if (1) begin : g\n"
      "    default disable iff rst1;\n" +
      FailingAt("a_g", "    ") + "    if (1) begin : gi\n" +
      FailingAt("a_gi", "      ") +
      "    end\n"
      "    for (genvar i = 0; i < 1; i++) begin : gl\n" +
      FailingAt("a_gl", "      ") +
      "    end\n"
      "  end\n"
      "  if (1) begin : sib\n" +
      FailingAt("a_sib", "    ") + "  end\n" + FailingAt("a_out"));
  EXPECT_EQ(ReportTimes(out, "a_g"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_gi"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_gl"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_sib"), "15 25 35");
  EXPECT_EQ(ReportTimes(out, "a_out"), "15 25 35");
}

}  // namespace
