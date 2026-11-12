#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ExpressionOperandSim, EveryKindOfOperandYieldsItsValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t(input a, output b);\n"
                 "  specify specparam SP = 4'b0110; endspecify\n"
                 "  parameter logic [7:0] P = 8'h3C;\n"
                 "  typedef struct packed { logic [3:0] h, l; } s_t;\n"
                 "  typedef union packed { logic [7:0] w; s_t s; } u_t;\n"
                 "  typedef struct { int x; int y; } us_t;\n"
                 "  u_t u = 8'hA5;\n"
                 "  wire [7:0] n = 8'h96;\n"
                 "  function us_t mk(); return '{3, 4}; endfunction\n"
                 "  int ua [4] = '{1, 2, 3, 4};\n"
                 "  logic [1:0][3:0] pa = 8'h7E;\n"
                 "  initial #1 $display(\"%0d %h %h %h %h %0d %0d %h %h %s\",\n"
                 "      SP + 1, P[5:2], u.s.h, u.w[3:0], u[7:4], mk().y,\n"
                 "      ua[1] + ua[2], n[7:4], pa[1], \"str\");\n"
                 "endmodule\n",
                 f),
      "7 f a 5 a 4 5 9 7 str\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
