#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ExpressionSim, InsideValueNoMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 8'd4 inside {8'd3, 8'd5, 8'd7};\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ExpressionSim, InsideWildcardRhsMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [2:0] val;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    val = 3'b101;\n"
      "    x = val inside {3'b1?1};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, InsideRangeBoundaryInclusive) {
  SimFixture f;
  auto [x, y] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  logic x, y;\n"
                                 "  initial begin\n"
                                 "    x = 8'd5 inside {[8'd5:8'd10]};\n"
                                 "    y = 8'd10 inside {[8'd5:8'd10]};\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "y");
  EXPECT_EQ(x, 1u);
  EXPECT_EQ(y, 1u);
}

TEST(InsideOperatorElaboration, UnpackedArrayLeftOperandIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[3] = '{1, 2, 3};\n"
      "  int q[$] = {1, 2, 3};\n"
      "  bit r;\n"
      "  initial r = arr inside {q};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the left operand of inside shall be singular", 5,
                            "11.4.13"));
}

TEST(InsideOperatorElaboration, UnpackedArrayInTheSetIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[3] = '{1, 2, 3};\n"
      "  int x = 2;\n"
      "  bit r;\n"
      "  initial r = x inside {arr};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InsideElaboration, UnpackedSubArrayOrMemberLeftOperandReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int x; } inner_t;\n"
      "  typedef struct packed { int a; } p_t;\n"
      "  int m [2][2];\n"
      "  struct { int arr [2]; inner_t in; struct { int y; } nest;\n"
      "           int s; p_t pk; } st;\n"
      "  inner_t named;\n"
      "  bit b;\n"
      "  initial begin\n"
      "    b = m[0] inside {1, 2};\n"
      "    b = st.arr inside {1, 2};\n"
      "    b = st.in inside {1, 2};\n"
      "    b = st.nest inside {1, 2};\n"
      "    b = m[0][1] inside {1, 2};\n"
      "    b = st.s inside {1, 2};\n"
      "    b = st.pk inside {1, 2};\n"
      "    b = named.x inside {1, 2};\n"
      "    b = st.in.x inside {1, 2};\n"
      "    b = st.arr[0] inside {1, 2};\n"
      "    b = st.zz inside {1, 2};\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {10u, 11u, 12u, 13u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the left operand of inside shall be singular",
                              line, "11.4.13"));
  }
  for (uint32_t line : {14u, 15u, 16u, 17u, 18u, 19u, 20u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "the left operand of inside shall be singular",
                               line, "11.4.13"));
  }
}

}  // namespace
