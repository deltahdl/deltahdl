#include "helpers_preprocess_and_get.h"

// §22.12: the `line directive shall set the line number of the following line.
// The only way to observe that renumbering flow through to a simulated value is
// to read it back via `__LINE__, whose expansion the preprocessor derives from
// the current (possibly overridden) line counter. Each test below assigns
// `__LINE__ to a variable AFTER a `line override and checks that the simulated
// result is the overridden number, not the natural source line - so the
// assertion fails if the override were ignored downstream.

TEST(LineDirectiveSimulation, OverriddenLineNumberReachesSimulatedValue) {
  // The `line directive sits on source line 3; the assignment on the
  // immediately following line therefore reports exactly the specified number
  // (800), whereas the natural line would be 4.
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
  // A `line directive placed between two module definitions renumbers the
  // remaining lines: the directive is on source line 5, so `__LINE__ on source
  // line 8 reports 500 + (8 - 5 - 1) == 502.
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
