#include <gtest/gtest.h>

#include <string>

#include "helpers_disable_iff_runs.h"

using namespace delta;

namespace {

std::string Leaves() {
  return "module leaf(input logic a, b, clk);\n" + FailingAt("a_leaf") +
         "endmodule\n"
         "interface ifc(input logic a, b, clk);\n" +
         FailingAt("a_ifc") +
         "endinterface\n"
         "program prg(input logic a, b, clk);\n" +
         FailingAt("a_prg") + "endprogram\n";
}

std::string RunHolder(const std::string& holder, const std::string& top) {
  return RunDisableIffDesign(Leaves() + holder, top);
}

constexpr const char* kInstance = "  m1 u1(a, b, clk, rst, rst1);\n";

TEST(DisableIffInstanceRun, InstancesUnderAModulesDefaultTakeNoCondition) {
  std::string out = RunHolder(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  default disable iff rst1;\n"
      "  ifc u_ifc(a, b, clk);\n"
      "  prg u_prg(a, b, clk);\n"
      "  leaf arr[1:0](a, b, clk);\n"
      "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_ifc"), "15 25 35");
  EXPECT_EQ(ReportTimes(out, "a_prg"), "15 25 35");
  EXPECT_EQ(ReportTimes(out, "a_leaf"), "15 15 25 25 35 35");
}

TEST(DisableIffInstanceRun, ABoundInstanceTakesNoCondition) {
  std::string out = RunHolder(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  default disable iff rst1;\n"
      "endmodule\n",
      std::string(kInstance) + "  bind m1 leaf bl(a, b, clk);\n");
  EXPECT_EQ(ReportTimes(out, "a_leaf"), "15 25 35");
}

TEST(DisableIffInstanceRun, InstancesInANestedGenerateBlockTakeNoCondition) {
  std::string out = RunHolder(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  default disable iff rst1;\n"
      "  if (1) begin : g\n"
      "    leaf u_leaf(a, b, clk);\n"
      "    ifc u_ifc(a, b, clk);\n"
      "    prg u_prg(a, b, clk);\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : l\n"
      "    leaf u_leaf(a, b, clk);\n"
      "    ifc u_ifc(a, b, clk);\n"
      "    prg u_prg(a, b, clk);\n"
      "  end\n"
      "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_leaf"), "15 15 25 25 35 35");
  EXPECT_EQ(ReportTimes(out, "a_ifc"), "15 15 25 25 35 35");
  EXPECT_EQ(ReportTimes(out, "a_prg"), "15 15 25 25 35 35");
}

TEST(DisableIffInstanceRun, InstancesOfNestedDeclarationsInherit) {
  std::string out = RunHolder(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  default disable iff rst1;\n"
      "  module nm;\n" +
          FailingAt("a_nm", "    ") +
          "  endmodule\n"
          "  interface ni;\n" +
          FailingAt("a_ni", "    ") +
          "  endinterface\n"
          "  program np;\n" +
          FailingAt("a_np", "    ") +
          "  endprogram\n"
          "  nm u_nm();\n"
          "  ni u_ni();\n"
          "  np u_np();\n"
          "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_nm"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_ni"), "15 25");
  EXPECT_EQ(ReportTimes(out, "a_np"), "15 25");
}

TEST(DisableIffInstanceRun, InstancesUnderAnInterfacesDefault) {
  std::string out = RunHolder(
      "interface hold(input logic a, b, clk, rst1);\n"
      "  default disable iff rst1;\n"
      "  ifc u_ifc(a, b, clk);\n"
      "  prg u_prg(a, b, clk);\n"
      "  interface ni;\n" +
          FailingAt("a_ni", "    ") +
          "  endinterface\n"
          "  ni u_ni();\n"
          "endinterface\n",
      "  hold u_hold(a, b, clk, rst1);\n");
  EXPECT_EQ(ReportTimes(out, "a_ifc"), "15 25 35");
  EXPECT_EQ(ReportTimes(out, "a_prg"), "15 25 35");
  EXPECT_EQ(ReportTimes(out, "a_ni"), "15 25");
}

TEST(DisableIffInstanceRun,
     InstancesUnderAGenerateBlocksDefaultTakeNoCondition) {
  std::string out = RunHolder(
      "module m1(input logic a, b, clk, rst, rst1);\n"
      "  if (1) begin : g\n"
      "    default disable iff rst1;\n"
      "    leaf u_leaf(a, b, clk);\n"
      "    ifc u_ifc(a, b, clk);\n"
      "    prg u_prg(a, b, clk);\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : l\n"
      "    default disable iff rst1;\n"
      "    leaf u_leaf(a, b, clk);\n"
      "    ifc u_ifc(a, b, clk);\n"
      "    prg u_prg(a, b, clk);\n"
      "  end\n"
      "endmodule\n",
      kInstance);
  EXPECT_EQ(ReportTimes(out, "a_leaf"), "15 15 25 25 35 35");
  EXPECT_EQ(ReportTimes(out, "a_ifc"), "15 15 25 25 35 35");
  EXPECT_EQ(ReportTimes(out, "a_prg"), "15 15 25 25 35 35");
}

}  // namespace
