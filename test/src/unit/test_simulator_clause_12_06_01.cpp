// §12.6.1: Pattern matching in case statements.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §12.6.1: Constant expression pattern — match selects the item.
TEST(SimA60701, CaseMatchesConstantMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd2: x = 8'd20;\n"
      "      8'd3: x = 8'd30;\n"
      "      default: x = 8'd0;\n"
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

// §12.6.1: No match → default item is executed.
TEST(SimA60701, CaseMatchesDefaultFallthrough) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd2: x = 8'd20;\n"
      "      default: x = 8'd77;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §12.6.1: Linear search — first matching item wins.
TEST(SimA60701, CaseMatchesFirstMatchWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      default: x = 8'd0;\n"
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

// §12.6.1: Pattern with &&& guard — pattern matches and guard is true.
TEST(SimA60701, CaseMatchesGuardTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    en = 1'b1;\n"
      "    case(sel) matches\n"
      "      8'd5 &&& en: x = 8'd10;\n"
      "      default: x = 8'd0;\n"
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

// §12.6.1: Pattern matches but guard is false — item not selected.
TEST(SimA60701, CaseMatchesGuardFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    en = 1'b0;\n"
      "    case(sel) matches\n"
      "      8'd5 &&& en: x = 8'd10;\n"
      "      default: x = 8'd99;\n"
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
  // Guard false → falls through to default.
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §12.6.1: Guard false on first item, second item matches.
TEST(SimA60701, CaseMatchesGuardFalseSecondMatches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel) matches\n"
      "      8'd5 &&& 1'b0: x = 8'd10;\n"
      "      8'd5: x = 8'd20;\n"
      "      default: x = 8'd0;\n"
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
  // First item: pattern matches but guard false → skip. Second matches.
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.6.1: casez with matches — z bits in pattern are wildcards.
TEST(SimA60701, CasezMatchesWildcard) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    casez(sel) matches\n"
      "      4'b1???: x = 8'd1;\n"
      "      4'b0???: x = 8'd2;\n"
      "      default: x = 8'd0;\n"
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

// §12.6.1: priority case matches — no match → violation.
TEST(SimA60701, PriorityCaseMatchesNoMatchViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd0;\n"
      "    priority case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd2: x = 8'd20;\n"
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

// §12.6.1: unique case matches — overlap detection.
TEST(SimA60701, UniqueCaseMatchesOverlapViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    unique case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
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
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §12.6.1: No match, no default — no statement executed.
TEST(SimA60701, CaseMatchesNoMatchNoDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd42;\n"
      "    case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd2: x = 8'd20;\n"
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
  // x retains its initial value.
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
