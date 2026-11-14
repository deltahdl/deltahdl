#include <gtest/gtest.h>

#include <string>

#include "helpers_disable_iff_runs.h"

using namespace delta;

namespace {

constexpr const char* kHead =
    "module m1(input logic a, b, clk, rst, rst1);\n"
    "  default disable iff rst1;\n";

constexpr const char* kInstance = "  m1 u1(a, b, clk, rst, rst1);\n";

std::string RunUnderOuterDefault(const std::string& body) {
  return RunDisableIffDesign(kHead + body + "endmodule\n", kInstance);
}

TEST(DisableIffNameResolutionRun,
     DISABLED_ANestedModulesLocalOfTheSameNameDoesNotCaptureTheDefault) {
  std::string out = RunUnderOuterDefault(
      "  module m2;\n"
      "    logic rst1 = 0;\n" +
      FailingAt("a_m2", "    ") + "  endmodule\n");
  EXPECT_EQ(ReportTimes(out, "a_m2"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     DISABLED_ALocalInAnIntermediateNestedModuleDoesNotCaptureTheDefault) {
  std::string out = RunUnderOuterDefault(
      "  module m2;\n"
      "    logic rst1 = 0;\n"
      "    module m3;\n" +
      FailingAt("a_m3", "      ") +
      "    endmodule\n"
      "  endmodule\n");
  EXPECT_EQ(ReportTimes(out, "a_m3"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     DISABLED_ANestedInterfacesOrProgramsLocalDoesNotCaptureTheDefault) {
  std::string out = RunUnderOuterDefault(
      "  interface ni;\n"
      "    logic rst1 = 0;\n" +
      FailingAt("a_ni", "    ") +
      "  endinterface\n"
      "  program np;\n"
      "    logic rst1 = 0;\n" +
      FailingAt("a_np", "    ") +
      "  endprogram\n"
      "  ni u_ni();\n"
      "  np u_np();\n");
  EXPECT_EQ(ReportTimes(out, "a_ni"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_np"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     DISABLED_AGenerateBlocksLocalVariableOrNetDoesNotCaptureTheDefault) {
  std::string out = RunUnderOuterDefault(
      "  if (1) begin : g1\n"
      "    logic rst1 = 0;\n" +
      FailingAt("a_g1", "    ") +
      "  end\n"
      "  if (1) begin : g2\n"
      "    wire rst1 = 1'b0;\n" +
      FailingAt("a_g2", "    ") +
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : lg\n"
      "    logic rst1 = 0;\n" +
      FailingAt("a_lg", "    ") +
      "  end\n"
      "  case (1)\n"
      "    1: begin : cg\n"
      "      logic rst1 = 0;\n" +
      FailingAt("a_cg", "      ") +
      "    end\n"
      "  endcase\n");
  EXPECT_EQ(ReportTimes(out, "a_g1"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_g2"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_lg"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_cg"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     DISABLED_AnInnerGenerateBlocksLocalDoesNotCaptureABlocksDefault) {
  std::string out = RunDisableIffDesign(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  if (1) begin : g\n"
      "    default disable iff rst1;\n"
      "    if (1) begin : h\n"
      "      logic rst1 = 0;\n" +
          FailingAt("a_h", "      ") +
          "    end\n"
          "  end\n"
          "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_h"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     DISABLED_AFunctionRedeclaredInAGenerateBlockDoesNotCaptureTheDefault) {
  std::string out = RunDisableIffDesign(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  function automatic logic f(logic x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  default disable iff f(rst1);\n"
      "  if (1) begin : g\n"
      "    function automatic logic f(logic x);\n"
      "      return 1'b0;\n"
      "    endfunction\n" +
          FailingAt("a_g", "    ") +
          "  end\n"
          "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_g"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     DISABLED_OneRedeclaredNameOfSeveralDoesNotCaptureTheDefault) {
  std::string out = RunDisableIffDesign(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  default disable iff rst1 && !rst;\n"
      "  if (1) begin : g\n"
      "    logic rst = 1;\n" +
          FailingAt("a_g", "    ") +
          "  end\n"
          "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_g"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     AHierarchicalNameIsFoundFromTheDeclaringScope) {
  std::string out = RunDisableIffDesign(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  if (1) begin : s\n"
      "    logic r;\n"
      "    assign r = rst1;\n"
      "  end\n"
      "  default disable iff s.r;\n"
      "  if (1) begin : g\n"
      "    if (1) begin : s\n"
      "      logic r = 0;\n"
      "    end\n" +
          FailingAt("a_g", "    ") +
          "  end\n"
          "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_g"), "15 25");
}

TEST(DisableIffNameResolutionRun,
     ANamedProceduralBlocksLocalDoesNotCaptureTheDefault) {
  std::string out = RunUnderOuterDefault(
      "  always @(posedge clk) begin : blk\n"
      "    static logic rst1 = 0;\n"
      "    a_blk: assert property (a |=> b) "
      "else $display(\"a_blk at %0d\", $time);\n"
      "  end\n");
  EXPECT_EQ(ReportTimes(out, "a_blk"), "15 25");
}

}  // namespace
