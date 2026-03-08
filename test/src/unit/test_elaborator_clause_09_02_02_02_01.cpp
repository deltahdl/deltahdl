// Non-LRM tests

#include <unordered_set>
#include "builders_sensitivity.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Elaborator, AlwaysCombSensitivityInferred) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->processes.empty());
  const auto& proc = mod->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_FALSE(proc.sensitivity.empty());

  bool found_a = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
  }
  EXPECT_TRUE(found_a);
}

TEST(SimCh4, AlwaysCombReEvaluatesOnChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    sel = 8'd0;\n"
      "    #5 sel = 8'd1;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = b;\n"
      "    else\n"
      "      result = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(SimCh9, AlwaysCombFunctionCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic logic [7:0] add_one(input logic [7:0] x);\n"
      "    return x + 8'd1;\n"
      "  endfunction\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd9;\n"
      "  always_comb begin\n"
      "    result = add_one(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(SimCh9b, AlwaysCombConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] y;\n"
      "  always_comb y = {hi, lo};\n"
      "  initial begin\n"
      "    hi = 4'hA;\n"
      "    lo = 4'h5;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0xA5u);
}

TEST(SimCh9b, AlwaysCombRetriggersOnChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, y;\n"
      "  always_comb y = a + 1;\n"
      "  initial begin\n"
      "    a = 10;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 11u);
}

TEST(SimCh9b, AlwaysCombSensitivityRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  const auto& procs = f.ctx.GetSensitiveProcesses("a");
  EXPECT_FALSE(procs.empty());
}

// §9.2.2.2.1: Variables also written in the block are excluded from
// sensitivity.
TEST(ElabClause09_02_02_02_01, WrittenVarsExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, temp;\n"
      "  always_comb begin\n"
      "    temp = a;\n"
      "    b = temp;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlwaysComb);
  bool found_a = false, found_temp = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "temp") found_temp = true;
  }
  EXPECT_TRUE(found_a);
  EXPECT_FALSE(found_temp);
}

// §9.2.2.2.1: Block-local variables excluded from sensitivity.
TEST(ElabClause09_02_02_02_01, BlockLocalVarsExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    logic local_var;\n"
      "    local_var = a;\n"
      "    b = local_var;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_a = false, found_local = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "local_var") found_local = true;
  }
  EXPECT_TRUE(found_a);
  EXPECT_FALSE(found_local);
}

// §9.2.2.2.1: Multiple read signals all appear in sensitivity.
TEST(ElabClause09_02_02_02_01, MultipleReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, c, y;\n"
      "  always_comb y = a & b | c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_a = false, found_b = false, found_c = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "b") found_b = true;
    if (ev.signal && ev.signal->text == "c") found_c = true;
  }
  EXPECT_TRUE(found_a);
  EXPECT_TRUE(found_b);
  EXPECT_TRUE(found_c);
}

// §9.2.2.2.1: LHS output variable not in sensitivity when only written.
TEST(ElabClause09_02_02_02_01, OutputOnlyVarNotInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_y = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "y") found_y = true;
  }
  EXPECT_FALSE(found_y);
}

// §9.2.2.2.1: Sensitivity uses longest static prefix for array access.
TEST(ElabClause09_02_02_02_01, ArrayAccessLongestStaticPrefix) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [1:0] addr;\n"
      "  logic [7:0] data;\n"
      "  always_comb data = mem[addr];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_mem = false, found_addr = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "mem") found_mem = true;
    if (ev.signal && ev.signal->text == "addr") found_addr = true;
  }
  EXPECT_TRUE(found_mem);
  EXPECT_TRUE(found_addr);
}

// §9.2.2.2.1: If condition and both branches contribute to sensitivity.
TEST(ElabClause09_02_02_02_01, IfConditionInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_sel = false, found_a = false, found_b = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "sel") found_sel = true;
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "b") found_b = true;
  }
  EXPECT_TRUE(found_sel);
  EXPECT_TRUE(found_a);
  EXPECT_TRUE(found_b);
}

// §9.2.2.2.1: Sensitivity edges are all kNone (level-sensitive).
TEST(ElabClause09_02_02_02_01, SensitivityEdgesAreNone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  for (const auto& ev : proc.sensitivity) {
    EXPECT_EQ(ev.edge, Edge::kNone);
  }
}

// §9.2.2.2.2: Variables read inside case branches are in sensitivity.
TEST(AlwaysCombCaseSensitivity, CaseBodyReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic a, b, y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = a;\n"
      "      2'b01: y = b;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_sel = false, found_a = false, found_b = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "sel") found_sel = true;
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "b") found_b = true;
  }
  EXPECT_TRUE(found_sel);
  EXPECT_TRUE(found_a);
  EXPECT_TRUE(found_b);
}

// §9.2.2.2.2: Immediate assertion expression contributes to sensitivity.
TEST(AssertExprInSensitivity, AssertExprInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, c, y;\n"
      "  always_comb begin\n"
      "    y = a & b;\n"
      "    assert (c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_c = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "c") found_c = true;
  }
  EXPECT_TRUE(found_c);
}

}  // namespace
