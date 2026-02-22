// Tests for A.8.6 — Operators — Simulation

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

struct SimA86Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA86Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

// =============================================================================
// A.8.6 Operators — unary_operator — Simulation
// =============================================================================

// § unary_operator — unary plus (identity)

TEST(SimA86, UnaryPlus) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = +8'd42;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// § unary_operator — unary minus (negate)

TEST(SimA86, UnaryMinus) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = -8'd1;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// § unary_operator — logical NOT

TEST(SimA86, UnaryLogicalNot) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = !1'b0;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § unary_operator — bitwise NOT

TEST(SimA86, UnaryBitwiseNot) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin x = 8'h0F; x = ~x; end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xF0u);
}

// § unary_operator — reduction AND

TEST(SimA86, UnaryReductionAnd) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = &8'hFF;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § unary_operator — reduction NAND

TEST(SimA86, UnaryReductionNand) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = ~&8'hFF;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unary_operator — reduction OR

TEST(SimA86, UnaryReductionOr) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = |8'h00;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unary_operator — reduction NOR

TEST(SimA86, UnaryReductionNor) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = ~|8'h00;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § unary_operator — reduction XOR

TEST(SimA86, UnaryReductionXor) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = ^8'hA5;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // A5 = 10100101, popcount=4 (even), XOR reduction = 0
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unary_operator — reduction XNOR (~^)

TEST(SimA86, UnaryReductionXnor) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = ~^8'hA5;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // ~^(A5) = ~(XOR reduction) = ~0 = 1
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § unary_operator — reduction XNOR (^~)

TEST(SimA86, UnaryReductionXnorAlt) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = ^~8'hA5;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (arithmetic) — Simulation
// =============================================================================

// § binary_operator — addition

TEST(SimA86, BinaryAdd) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd10 + 8'd20;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// § binary_operator — subtraction

TEST(SimA86, BinarySub) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd30 - 8'd12;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 18u);
}

// § binary_operator — multiplication

TEST(SimA86, BinaryMul) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd7 * 8'd6;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// § binary_operator — division

TEST(SimA86, BinaryDiv) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd100 / 8'd5;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// § binary_operator — modulo

TEST(SimA86, BinaryMod) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd17 % 8'd5;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// § binary_operator — power

TEST(SimA86, BinaryPower) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd2 ** 8'd5;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 32u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (equality) — Simulation
// =============================================================================

// § binary_operator — == (true)

TEST(SimA86, BinaryEqTrue) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd10 == 8'd10);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — != (true)

TEST(SimA86, BinaryNeqTrue) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd10 != 8'd5);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — === (case equality)

TEST(SimA86, BinaryCaseEq) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd7 === 8'd7);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — !== (case inequality)

TEST(SimA86, BinaryCaseNeq) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd7 !== 8'd3);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — ==? (wildcard equality)

TEST(SimA86, BinaryWildcardEq) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd5 ==? 8'd5);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — !=? (wildcard inequality)

TEST(SimA86, BinaryWildcardNeq) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd5 !=? 8'd3);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (logical) — Simulation
// =============================================================================

// § binary_operator — && (logical AND)

TEST(SimA86, BinaryLogicalAnd) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd1 && 8'd1);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — || (logical OR)

TEST(SimA86, BinaryLogicalOr) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd0 || 8'd1);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (relational) — Simulation
// =============================================================================

// § binary_operator — < (less than)

TEST(SimA86, BinaryLessThan) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd3 < 8'd5);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — > (greater than)

TEST(SimA86, BinaryGreaterThan) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd10 > 8'd3);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — >= (greater or equal)

TEST(SimA86, BinaryGreaterOrEqual) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (8'd5 >= 8'd5);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (bitwise) — Simulation
// =============================================================================

// § binary_operator — & (bitwise AND)

TEST(SimA86, BinaryBitwiseAnd) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'hF0 & 8'h3C;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x30u);
}

// § binary_operator — | (bitwise OR)

TEST(SimA86, BinaryBitwiseOr) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'hF0 | 8'h0F;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// § binary_operator — ^ (bitwise XOR)

TEST(SimA86, BinaryBitwiseXor) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'hFF ^ 8'h0F;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

// § binary_operator — ^~ (bitwise XNOR)

TEST(SimA86, BinaryBitwiseXnor) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'hFF ^~ 8'h0F;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// =============================================================================
// A.8.6 Operators — binary_operator (shift) — Simulation
// =============================================================================

// § binary_operator — << (logical left shift)

TEST(SimA86, BinaryLogicalLeftShift) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd1 << 4;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

// § binary_operator — >> (logical right shift)

TEST(SimA86, BinaryLogicalRightShift) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd128 >> 3;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

// § binary_operator — <<< (arithmetic left shift)

TEST(SimA86, BinaryArithLeftShift) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd3 <<< 2;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

// § binary_operator — >>> (arithmetic right shift)

TEST(SimA86, BinaryArithRightShift) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'd64 >>> 2;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (implication) — Simulation
// =============================================================================

// § binary_operator — -> (implication: 0->x is always 1)

TEST(SimA86, BinaryImplication) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (1'b0 -> 1'b0);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — <-> (equivalence: same values => 1)

TEST(SimA86, BinaryEquivalence) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic x;\n"
                              "  initial x = (1'b1 <-> 1'b1);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// =============================================================================
// A.8.6 Operators — inc_or_dec_operator — Simulation
// =============================================================================

// § inc_or_dec_operator — prefix ++

TEST(SimA86, PrefixIncrement) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x;\n"
                              "  initial begin x = 10; ++x; end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// § inc_or_dec_operator — prefix --

TEST(SimA86, PrefixDecrement) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x;\n"
                              "  initial begin x = 10; --x; end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// § inc_or_dec_operator — postfix ++

TEST(SimA86, PostfixIncrement) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x;\n"
                              "  initial begin x = 10; x++; end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// § inc_or_dec_operator — postfix --

TEST(SimA86, PostfixDecrement) {
  SimA86Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x;\n"
                              "  initial begin x = 10; x--; end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}
