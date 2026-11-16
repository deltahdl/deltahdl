#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(UrandomRun, TheSameSeedFromAnyIntegralExpressionReplaysTheSequence) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  parameter int SEED = 254;\n"
      "  int unsigned a[8], b[8];\n"
      "  int i, sv = 254, same = 0, diverged = 0;\n"
      "  function automatic int agreeing();\n"
      "    int n = 0;\n"
      "    for (int j = 0; j < 8; j++) if (a[j] == b[j]) n++;\n"
      "    return n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = $urandom(254);\n"
      "    for (i = 1; i < 8; i++) a[i] = $urandom;\n"
      "    b[0] = $urandom(SEED);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    same += agreeing();\n"
      "    b[0] = $urandom(250 + 4);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    same += agreeing();\n"
      "    b[0] = $urandom(sv);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    same += agreeing();\n"
      "    b[0] = $urandom(255);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    diverged = agreeing() < 8;\n"
      "    $display(\"%0d %0d\", same, diverged);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "24 1\n");
}

TEST(UrandomRun, EachCallIsANewUnsignedThirtyTwoBitNumber) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [63:0] wide;\n"
      "  int unsigned r, prev;\n"
      "  int i, advanced = 0, upper_zero = 0, high = 0;\n"
      "  initial begin\n"
      "    prev = $urandom;\n"
      "    for (i = 0; i < 32; i++) begin\n"
      "      r = $urandom;\n"
      "      if (r != prev) advanced++;\n"
      "      prev = r;\n"
      "      wide = $urandom;\n"
      "      if (wide[63:32] == 0) upper_zero++;\n"
      "      if (wide[31]) high = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", advanced, upper_zero, high);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

TEST(UrandomRun, EmptyParenthesesDrawFromTheSameSequence) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int unsigned a, b, z;\n"
      "  initial begin\n"
      "    z = $urandom(3);\n"
      "    a = $urandom();\n"
      "    z = $urandom(3);\n"
      "    b = $urandom;\n"
      "    $display(\"%0d\", a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(UrandomRun, TheResultIsUnsignedAsAnOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  longint w;\n"
      "  initial begin\n"
      "    w = $urandom(9) | 32'h8000_0000;\n"
      "    $display(\"%0d %0d\", $urandom > -1, w > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

TEST(UrandomRun, AClassMethodAndAPackageFunctionReplayASeed) {
  SimFixture f;
  std::string out = RunCapture(
      "package q;\n"
      "  function automatic bit [63:0] two(int s);\n"
      "    two[63:32] = $urandom(s);\n"
      "    two[31:0] = $urandom;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  class C;\n"
      "    function bit [63:0] two(int s);\n"
      "      two[63:32] = $urandom(s);\n"
      "      two[31:0] = $urandom;\n"
      "    endfunction\n"
      "  endclass\n"
      "  bit [63:0] a, b, c, d;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    a = o.two(11);\n"
      "    b = o.two(11);\n"
      "    c = q::two(12);\n"
      "    d = q::two(12);\n"
      "    $display(\"%0d %0d %0d\", a == b, c == d, a[63:32] != a[31:0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

}  // namespace
