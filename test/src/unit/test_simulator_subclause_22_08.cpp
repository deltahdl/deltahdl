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
