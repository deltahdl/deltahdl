#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysStarSim, AlwaysStarIfElseTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @*\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'hBB;\n"
      "    sel = 1;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0xAAu);
}

TEST(AlwaysStarSim, AlwaysStarCaseStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] y;\n"
      "  always @*\n"
      "    case (sel)\n"
      "      2'b00: y = 8'h10;\n"
      "      2'b01: y = 8'h20;\n"
      "      2'b10: y = 8'h30;\n"
      "      default: y = 8'hFF;\n"
      "    endcase\n"
      "  initial begin\n"
      "    sel = 2'b10;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

TEST(AlwaysStarSim, AlwaysStarAllRhsSensitive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, y;\n"
      "  always @* y = a + b + c;\n"
      "  initial begin\n"
      "    a = 8'h10;\n"
      "    b = 8'h20;\n"
      "    c = 8'h03;\n"
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

  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

TEST(AlwaysStarSim, AlwaysStarParenForm) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @(*) y = a | b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

TEST(AlwaysStarSim, AlwaysStarTernaryOp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = sel ? a : b;\n"
      "  initial begin\n"
      "    a = 8'hDE;\n"
      "    b = 8'hAD;\n"
      "    sel = 0;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0xADu);
}

TEST(AlwaysStarSim, AlwaysStarConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] y;\n"
      "  always @* y = {hi, lo};\n"
      "  initial begin\n"
      "    hi = 4'hC;\n"
      "    lo = 4'h3;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0xC3u);
}

TEST(AlwaysStarSim, AlwaysStarBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [7:0] copy;\n"
      "  logic y;\n"
      "  always @* begin\n"
      "    copy = data;\n"
      "    y = data[5];\n"
      "  end\n"
      "  initial begin\n"
      "    data = 8'b0010_0000;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(AlwaysStarSim, AlwaysStarFunctionCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function logic [7:0] add3(input logic [7:0] x);\n"
      "    return x + 3;\n"
      "  endfunction\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = add3(a);\n"
      "  initial begin\n"
      "    a = 8'h10;\n"
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

  EXPECT_EQ(y->value.ToUint64(), 0x13u);
}

TEST(AlwaysStarSim, AlwaysStarMultipleOutputs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum, diff;\n"
      "  always @* begin\n"
      "    sum = a + b;\n"
      "    diff = a - b;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'h30;\n"
      "    b = 8'h10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* sum = f.ctx.FindVariable("sum");
  auto* diff = f.ctx.FindVariable("diff");
  ASSERT_NE(sum, nullptr);
  ASSERT_NE(diff, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 0x40u);
  EXPECT_EQ(diff->value.ToUint64(), 0x20u);
}

TEST(AlwaysStarSim, AlwaysStarLocalVar) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* begin\n"
      "    logic [7:0] tmp;\n"
      "    tmp = a + b;\n"
      "    y = tmp;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

TEST(AlwaysStarSim, MultipleAlwaysStarIndependent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d, x, y;\n"
      "  always @* x = a & b;\n"
      "  always @* y = c | d;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h0F;\n"
      "    c = 8'hA0;\n"
      "    d = 8'h05;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(y->value.ToUint64(), 0xA5u);
}

TEST(AlwaysStarSim, AlwaysStarResultWidthAndValue8) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = a;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
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
  EXPECT_EQ(y->value.width, 8u);
  EXPECT_EQ(y->value.ToUint64(), 0xABu);
}

TEST(AlwaysStarElab, PlainAlwaysWithStarSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @(*) b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

TEST(AlwaysStarElab, LhsIndexVarInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] y;\n"
      "  logic [2:0] a;\n"
      "  logic en;\n"
      "  always @* begin\n"
      "    y = 8'hff;\n"
      "    y[a] = !en;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("en")) << "en (RHS) must be in sensitivity";
  EXPECT_TRUE(names.count("a")) << "a (LHS index) must be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, ReadAfterWriteIntermediateInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  logic tmp1, tmp2, y;\n"
      "  always @* begin\n"
      "    tmp1 = a & b;\n"
      "    tmp2 = c & d;\n"
      "    y = tmp1 | tmp2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a"));
  EXPECT_TRUE(names.count("b"));
  EXPECT_TRUE(names.count("c"));
  EXPECT_TRUE(names.count("d"));
  EXPECT_TRUE(names.count("tmp1"))
      << "tmp1 (read-after-write intermediate) must be in sensitivity";
  EXPECT_TRUE(names.count("tmp2"))
      << "tmp2 (read-after-write intermediate) must be in sensitivity";
}

TEST(AlwaysStarElab, ReadModifyWriteInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  always @* begin\n"
      "    a = a + 1;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a"))
      << "a (appears on RHS) must be in sensitivity even though also on LHS";
}

TEST(AlwaysStarElab, CaseItemVarsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] state, next;\n"
      "  logic go;\n"
      "  always @* begin\n"
      "    next = 4'b0;\n"
      "    case (1'b1)\n"
      "      state[0]: if (go) next[1] = 1'b1;\n"
      "                else    next[0] = 1'b1;\n"
      "      state[1]:         next[2] = 1'b1;\n"
      "      state[2]:         next[3] = 1'b1;\n"
      "      state[3]:         next[0] = 1'b1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("state"))
      << "state (case item expression) must be in sensitivity";
  EXPECT_TRUE(names.count("go"))
      << "go (conditional expr) must be in sensitivity";
}

TEST(AlwaysStarElab, ConditionalExprInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always @* begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("sel"))
      << "sel (conditional expr) must be in sensitivity";
  EXPECT_TRUE(names.count("a"));
  EXPECT_TRUE(names.count("b"));
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, CaseSelectorExprInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] y;\n"
      "  always @(*) begin\n"
      "    case (sel)\n"
      "      2'b00: y = 8'h10;\n"
      "      2'b01: y = 8'h20;\n"
      "      default: y = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("sel"))
      << "sel (case selector) must be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, SubroutineArgInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function logic [7:0] inc(input logic [7:0] x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = inc(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a")) << "a (subroutine arg) must be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, BlockLocalExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* begin\n"
      "    logic [7:0] tmp;\n"
      "    tmp = a + b;\n"
      "    y = tmp;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a"));
  EXPECT_TRUE(names.count("b"));
  EXPECT_FALSE(names.count("tmp"))
      << "tmp (block-local) must not be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, DelayControlOnlyVarExcludedFromSensitivity) {
  // §9.4.2.2 exception 1: an identifier that appears only inside a timing
  // control (here a #delay) is not added to the implicit @* sensitivity list,
  // while a net/variable read by the controlled statement still is.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, y;\n"
      "  logic [7:0] dly;\n"
      "  always @* begin\n"
      "    #dly y = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a")) << "a (RHS read) must be in sensitivity";
  EXPECT_FALSE(names.count("dly"))
      << "dly (only in delay control) must not be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, EventControlOnlySignalExcludedFromSensitivity) {
  // §9.4.2.2 exception 1: an identifier that appears only inside an inner
  // event control (@(clk)) is excluded from the implicit @* list.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, y;\n"
      "  logic clk;\n"
      "  always @* begin\n"
      "    @(clk) y = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a")) << "a (RHS read) must be in sensitivity";
  EXPECT_FALSE(names.count("clk"))
      << "clk (only in event control) must not be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, WaitConditionOnlyVarExcludedFromSensitivity) {
  // §9.4.2.2 exception 1: an identifier that appears only in a wait condition
  // is excluded from the implicit @* list; the controlled statement's read
  // operands are still collected.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, y;\n"
      "  logic en;\n"
      "  always @* begin\n"
      "    wait (en) y = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a")) << "a (RHS read) must be in sensitivity";
  EXPECT_FALSE(names.count("en"))
      << "en (only in wait condition) must not be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, AtStarAndAtStarParenEquivalent) {
  ElabFixture f1;
  auto* d1 = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always @* y = a & b;\n"
      "endmodule\n",
      f1);
  ElabFixture f2;
  auto* d2 = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always @(*) y = a & b;\n"
      "endmodule\n",
      f2);
  ASSERT_NE(d1, nullptr);
  ASSERT_NE(d2, nullptr);
  EXPECT_FALSE(f1.has_errors);
  EXPECT_FALSE(f2.has_errors);
  auto& s1 = d1->top_modules[0]->processes[0].sensitivity;
  auto& s2 = d2->top_modules[0]->processes[0].sensitivity;
  EXPECT_EQ(s1.size(), s2.size());
  std::unordered_set<std::string> n1, n2;
  for (const auto& ev : s1)
    if (ev.signal) n1.insert(std::string(ev.signal->text));
  for (const auto& ev : s2)
    if (ev.signal) n2.insert(std::string(ev.signal->text));
  EXPECT_EQ(n1, n2);
}

TEST(AlwaysStarElab, RhsIndexVarInSensitivity) {
  // §9.4.2.2: a variable used as the index of a right-hand-side select is a
  // read appearing on the RHS, so it (and the selected vector) joins the
  // implicit @* list; the pure-LHS target does not.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] vec, y;\n"
      "  logic [2:0] idx;\n"
      "  always @* y = vec[idx];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("idx"))
      << "idx (RHS select index) must be in sensitivity";
  EXPECT_TRUE(names.count("vec"))
      << "vec (RHS selected vector) must be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

TEST(AlwaysStarElab, TimingControlSignalAlsoReadInSensitivity) {
  // §9.4.2.2 exception 1 boundary: the exclusion applies only to identifiers
  // that appear *exclusively* in timing controls. A signal used as a delay
  // value and also read by the controlled statement is still included.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] d, y;\n"
      "  always @* #d y = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("d"))
      << "d appears on the RHS as well, so it is not timing-control-only";
}

TEST(AlwaysStarElab, ConstantRhsProducesEmptySensitivity) {
  // §9.4.2.2: the implicit list is exactly the set of read nets/variables. A
  // body that reads nothing yields an empty list and is not an error.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] y;\n"
      "  always @* y = 8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_TRUE(mod->processes[0].sensitivity.empty())
      << "a constant RHS reads no signals, so the implicit list is empty";
}

}  // namespace
