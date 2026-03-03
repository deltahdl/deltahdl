// §11.4.5: Equality operators

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// § binary_operator — equality operators elaborate
TEST(ElabA86, BinaryCaseEqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 === 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryCaseNeqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !== 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// ---------------------------------------------------------------------------
// 25. always_comb with equality comparison.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombEqualityCheck) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic y;\n"
      "  always_comb y = (a == b);\n"
      "  initial begin\n"
      "    a = 8'h42;\n"
      "    b = 8'h42;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // a == b is true -> y = 1.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 20. Blocking assignment with comparison operators.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignComparisonOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int r_eq, r_ne, r_lt, r_gt, r_le, r_ge;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    r_eq = (a == b);\n"
      "    r_ne = (a != b);\n"
      "    r_lt = (a < b);\n"
      "    r_gt = (a > b);\n"
      "    r_le = (a <= b);\n"
      "    r_ge = (a >= b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_eq = f.ctx.FindVariable("r_eq");
  auto* r_ne = f.ctx.FindVariable("r_ne");
  auto* r_lt = f.ctx.FindVariable("r_lt");
  auto* r_gt = f.ctx.FindVariable("r_gt");
  auto* r_le = f.ctx.FindVariable("r_le");
  auto* r_ge = f.ctx.FindVariable("r_ge");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_ne, nullptr);
  ASSERT_NE(r_lt, nullptr);
  ASSERT_NE(r_gt, nullptr);
  ASSERT_NE(r_le, nullptr);
  ASSERT_NE(r_ge, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 0u);  // 10 == 20 -> false
  EXPECT_EQ(r_ne->value.ToUint64(), 1u);  // 10 != 20 -> true
  EXPECT_EQ(r_lt->value.ToUint64(), 1u);  // 10 < 20  -> true
  EXPECT_EQ(r_gt->value.ToUint64(), 0u);  // 10 > 20  -> false
  EXPECT_EQ(r_le->value.ToUint64(), 1u);  // 10 <= 20 -> true
  EXPECT_EQ(r_ge->value.ToUint64(), 0u);  // 10 >= 20 -> false
}

}  // namespace
