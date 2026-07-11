#include <iostream>
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Elaborates and simulates a single-module source, capturing stdout so the
// value a constant function folded into a localparam at elaboration time can be
// observed downstream at run time.
inline std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §13.4.3: a constant function call is evaluated at elaboration time. The
// resulting localparam value must be the one the running simulation sees. The
// LRM clogb2 example folds clogb2(256) to 8; printing addr_width at run time
// observes that folded value end-to-end.
TEST(ConstantFunctionSim, Clogb2ResultReachesRuntime) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function integer clogb2(input int value);\n"
      "    value = value - 1;\n"
      "    for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)\n"
      "      value = value >> 1;\n"
      "  endfunction\n"
      "  localparam addr_width = clogb2(256);\n"
      "  initial $display(\"%0d\", addr_width);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8\n");
}

// §13.4.3: the folded value is a genuine constant usable to size a vector. The
// bit width of a signal declared [P-1:0] with P = double_val(4) must be 8,
// observed at run time via $bits.
TEST(ConstantFunctionSim, FoldedValueSizesRuntimeSignal) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int double_val(int n); return n * 2; endfunction\n"
      "  localparam int P = double_val(4);\n"
      "  logic [P-1:0] bus;\n"
      "  initial $display(\"%0d %0d\", P, $bits(bus));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8 8\n");
}

// §13.4.3 / §11.2.1: a constant function call folds in a packed-dimension
// position, not only in a parameter initializer. `logic [calc(3)-1:0]` sizes
// the vector to 6 bits (calc(3) = 6), observed at run time via $bits.
TEST(ConstantFunctionSim, ConstFunctionCallInPackedDimension) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  logic [calc(3)-1:0] bus;\n"
      "  initial $display(\"%0d\", $bits(bus));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "6\n");
}

// §13.4.3: non-severity system task calls in a constant function are ignored
// during its elaboration-time evaluation. Folding compute(4) to initialize P is
// what makes "8" print; the $write inside the body must emit nothing, because
// the constant-function evaluation silently skips it. (compute is never called
// at run time, so the only place $write could fire is the elaboration-time
// fold.) Exact "8\n" therefore confirms both the fold and the ignore.
TEST(ConstantFunctionSim, SystemTaskInBodyProducesNoOutput) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int compute(int n);\n"
      "    $write(\"SIDEEFFECT\");\n"
      "    return n * 2;\n"
      "  endfunction\n"
      "  localparam int P = compute(4);\n"
      "  initial $display(\"%0d\", P);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8\n");
}

}  // namespace
