#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

TEST(DefaultNettypeSimulation, WireModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`default_nettype wire\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result", CuPropagation::kDefaultNetType);
  EXPECT_EQ(result, 42u);
}

static std::string PassThrough() {
  return "module p0(input logic i, output logic o);\n"
         "  assign o = i;\n"
         "endmodule\n";
}

TEST(DefaultNettypeSimulation, ATrailingDirectiveLeavesTheModulesBeforeIt) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`default_nettype tri1\n" + PassThrough() +
                                     "module t;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "  initial #1 $display(\"%b\", w);\n"
                                     "endmodule\n"
                                     "`default_nettype wire\n",
                                 f),
            "1\n");
}

TEST(DefaultNettypeSimulation, NoneBeforeAndAfterLeavesAWireModuleItsNets) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`default_nettype none\n" + PassThrough() +
                                     "`default_nettype wire\n"
                                     "module t;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "  initial #1 $display(\"%b\", w);\n"
                                     "endmodule\n"
                                     "`default_nettype none\n",
                                 f),
            "z\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DefaultNettypeSimulation, EachModuleTakesTheDirectiveBeforeIt) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(PassThrough() +
                                     "`default_nettype tri0\n"
                                     "module t0;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "endmodule\n"
                                     "`default_nettype tri1\n"
                                     "module t1;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "endmodule\n"
                                     "`default_nettype wire\n"
                                     "module t2;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "endmodule\n"
                                     "module t;\n"
                                     "  t0 a();\n"
                                     "  t1 b();\n"
                                     "  t2 c();\n"
                                     "  initial #1 $display(\"%b %b %b\", "
                                     "a.w, b.w, c.w);\n"
                                     "endmodule\n",
                                 f),
            "0 1 z\n");
}

static std::string RunNettype(const std::string& src) {
  SimFixture f;
  return PreprocessAndCapture(src, f);
}

static std::string TwoDrivers(const char* type) {
  return std::string("`default_nettype ") + type +
         "\nmodule t;\n  assign w = 1'b1;\n  assign w = 1'b0;\n"
         "  initial #1 $display(\"%b\", w);\nendmodule\n";
}

TEST(DefaultNettypeSimulation, NoneAcceptsADrivenExplicitNet) {
  EXPECT_EQ(RunNettype("`default_nettype none\nmodule t;\n  wire w;\n"
                       "  assign w = 1'b1;\n"
                       "  initial #1 $display(\"%b\", w);\nendmodule\n"),
            "1\n");
}

TEST(DefaultNettypeSimulation, AfterNoneThenResetallAnImplicitNetIsAWire) {
  EXPECT_EQ(RunNettype("`default_nettype none\n`resetall\nmodule t;\n"
                       "  assign w = 1'b1;\n"
                       "  initial #1 $display(\"%b\", w);\nendmodule\n"),
            "1\n");
}

TEST(DefaultNettypeSimulation, ImplicitNetsResolveByTheirType) {
  EXPECT_EQ(RunNettype(TwoDrivers("wor")), "1\n");
  EXPECT_EQ(RunNettype(TwoDrivers("triand")), "0\n");
  EXPECT_EQ(RunNettype(TwoDrivers("trior")), "1\n");
}

TEST(DefaultNettypeSimulation, AnImplicitTriregHoldsItsCharge) {
  EXPECT_EQ(RunNettype("`default_nettype trireg\nmodule t;\n"
                       "  logic en = 1;\n"
                       "  assign w = en ? 1'b1 : 1'bz;\n"
                       "  initial begin #1 en = 0; #1 $display(\"%b\", w); "
                       "end\nendmodule\n"),
            "1\n");
}

TEST(DefaultNettypeSimulation, InterfaceProgramAndGenerateNetsTakeTheType) {
  EXPECT_EQ(RunNettype("`default_nettype wand\ninterface i;\n"
                       "  assign w = 1'b1;\n  assign w = 1'b0;\n"
                       "  initial #1 $display(\"%b\", w);\nendinterface\n"
                       "module t; i ii(); endmodule\n"),
            "0\n");
  EXPECT_EQ(RunNettype("`default_nettype wor\nprogram p;\n"
                       "  assign w = 1'b1;\n  assign w = 1'b0;\n"
                       "  initial #1 $display(\"%b\", w);\nendprogram\n"
                       "module t; p pp(); endmodule\n"),
            "1\n");
  EXPECT_EQ(RunNettype("`default_nettype wand\nmodule t;\n"
                       "  if (1) begin : g\n    assign w = 1'b1;\n"
                       "    assign w = 1'b0;\n  end\n"
                       "  initial #1 $display(\"%b\", g.w);\nendmodule\n"),
            "0\n");
}

TEST(DefaultNettypeSimulation, DISABLED_APortExpressionIdentifierIsImplicit) {
  EXPECT_EQ(RunNettype("`default_nettype tri1\n"
                       "module c(input .P(x));\n"
                       "  initial #1 $display(\"%b\", x);\nendmodule\n"
                       "module t; c cc(); endmodule\n"),
            "1\n");
}
