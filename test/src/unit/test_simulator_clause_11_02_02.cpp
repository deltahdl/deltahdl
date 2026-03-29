#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AggregateExprSim, StructEqualityReturnsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic eq;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "    y = '{8'd1, 8'd2};\n"
      "    eq = (x == y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, StructEqualityReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic eq;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "    y = '{8'd3, 8'd4};\n"
      "    eq = (x == y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, StructInequalityReturnsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "    y = '{8'd3, 8'd4};\n"
      "    neq = (x != y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, StructInequalityReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    x = '{8'd5, 8'd10};\n"
      "    y = '{8'd5, 8'd10};\n"
      "    neq = (x != y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, StructCopiedInAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  initial begin\n"
      "    x = '{8'd42, 8'd99};\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* src = f.ctx.FindVariable("x");
  auto* dst = f.ctx.FindVariable("y");
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.ToUint64(), src->value.ToUint64());
}

TEST(AggregateExprSim, StructPassedToFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [15:0] a; logic [15:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  int result;\n"
      "  function automatic int sum(input pair_t s);\n"
      "    return s.a + s.b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    p = '{16'd10, 16'd20};\n"
      "    result = sum(p);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

}  // namespace
