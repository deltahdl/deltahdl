#include <gtest/gtest.h>

#include "helpers_preprocess_and_get.h"

TEST(LineDirectiveSimulation, OverriddenLineNumberReachesSimulatedValue) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  int result;\n"
      "  `line 800 \"renamed.sv\" 0\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 800u);
}

TEST(LineDirectiveSimulation, OverrideBetweenModulesRenumbersFollowingLines) {
  auto result = PreprocessAndGet(
      "module m1;\n"
      "  int unused;\n"
      "  initial unused = 8'd10;\n"
      "endmodule\n"
      "`line 500 \"switched.sv\" 0\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 502u);
}
