// §12.5.4: Set membership case statement.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §12.5.4: Basic value match — case(sel) inside matches exact value.
TEST(SimA607, CaseInsideMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel) inside\n"
      "      8'd1, 8'd3: x = 8'd10;\n"
      "      8'd5: x = 8'd20;\n"
      "      default: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.5.4: No value matches → default is executed.
TEST(SimA607, CaseInsideDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    case(sel) inside\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd5: x = 8'd20;\n"
      "      default: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// §12.5.4: Comma-separated values in a single case item — first item matches.
TEST(SimA607, CaseInsideCommaValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd3;\n"
      "    case(sel) inside\n"
      "      8'd1, 8'd3, 8'd5: x = 8'd10;\n"
      "      8'd7: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.5.4: Range match [lo:hi] in case item.
TEST(SimA607, CaseInsideRangeMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel) inside\n"
      "      [8'd3:8'd7]: x = 8'd10;\n"
      "      default: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.5.4: Range match — value outside range → no match.
TEST(SimA607, CaseInsideRangeNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd10;\n"
      "    case(sel) inside\n"
      "      [8'd3:8'd7]: x = 8'd10;\n"
      "      default: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.5.4: Asymmetric wildcard — x/z bits in pattern are don't-cares.
TEST(SimA607, CaseInsideWildcardInPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 3'b100;\n"
      "    case(sel) inside\n"
      "      3'b1??: x = 3'd1;\n"
      "      default: x = 3'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.5.4: Asymmetric wildcard — x in selector does NOT match (no wildcard).
TEST(SimA607, CaseInsideXInSelectorNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 3'bx00;\n"
      "    x = 3'd0;\n"
      "    case(sel) inside\n"
      "      3'b100: x = 3'd1;\n"
      "      3'b000: x = 3'd2;\n"
      "      default: x = 3'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x in selector → no value matches → default
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §12.5.4: unique case inside with overlap → violation.
TEST(SimA607, UniqueCaseInsideOverlapViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    unique case(sel) inside\n"
      "      [8'd1:8'd10]: x = 8'd10;\n"
      "      [8'd3:8'd7]: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // First matching item is executed.
  EXPECT_EQ(var->value.ToUint64(), 10u);
  // Overlap detected → violation.
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §12.5.4: priority case inside, no match → violation.
TEST(SimA607, PriorityCaseInsideNoMatchViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd0;\n"
      "    priority case(sel) inside\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd5: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §12.5.4: LRM example — priority casez with bit patterns.
TEST(SimA607, CaseInsideLRMExample) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] status;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    status = 3'b001;\n"
      "    priority case (status) inside\n"
      "      3'd1, 3'd3: x = 8'd1;\n"
      "      [3'd4:3'd7]: x = 8'd2;\n"
      "      default: x = 8'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // status=1 matches first item (1, 3)
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
