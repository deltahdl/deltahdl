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

struct SimA60701Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimA60701Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.6.7.1 Patterns — Simulation tests
// =============================================================================

// ---------------------------------------------------------------------------
// assignment_pattern: positional — simulation
// ---------------------------------------------------------------------------

// §10.9: positional assignment pattern packs elements MSB-first
TEST(SimA60701, PositionalPatternPacksMSBFirst) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd1, 8'd2} = {8'h01, 8'h02} = 16'h0102 = 258
  EXPECT_EQ(var->value.ToUint64(), 258u);
}

// §10.9: single-element positional pattern
TEST(SimA60701, SingleElementPositionalPattern) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §10.9: four-element positional pattern
TEST(SimA60701, FourElementPositionalPattern) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2, 8'd3, 8'd4};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd1, 8'd2, 8'd3, 8'd4} = 32'h01020304 = 16909060
  EXPECT_EQ(var->value.ToUint64(), 0x01020304u);
}

// ---------------------------------------------------------------------------
// assignment_pattern: named struct — simulation
// ---------------------------------------------------------------------------

// §10.9.2: named assignment pattern for struct initialization
TEST(SimA60701, NamedStructPatternInit) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, b: 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // a=10 in upper byte, b=20 in lower byte: (10 << 8) | 20 = 2580
  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

// §10.9.2: named pattern with reversed field order
TEST(SimA60701, NamedStructPatternReversedOrder) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{b: 8'd20, a: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // Same result as above regardless of key order: (10 << 8) | 20 = 2580
  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

// §10.9.2: named pattern with default key fills remaining fields
TEST(SimA60701, NamedStructPatternWithDefault) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, default: 8'd99};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // a=10 (explicit), b=99 (default): (10 << 8) | 99 = 2659
  EXPECT_EQ(var->value.ToUint64(), 2659u);
}

// §10.9.2: named pattern with only default key
TEST(SimA60701, NamedStructPatternOnlyDefault) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{default: 8'd55};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // Both a=55, b=55: (55 << 8) | 55 = 14135
  EXPECT_EQ(var->value.ToUint64(), 14135u);
}

// ---------------------------------------------------------------------------
// assignment_pattern: positional struct — simulation
// ---------------------------------------------------------------------------

// §10.9: positional assignment pattern for struct
TEST(SimA60701, PositionalStructPatternInit) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd3, 8'd7};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // a=3 in upper byte, b=7 in lower byte: (3 << 8) | 7 = 775
  EXPECT_EQ(var->value.ToUint64(), 775u);
}

// ---------------------------------------------------------------------------
// assignment_pattern: struct with three fields — simulation
// ---------------------------------------------------------------------------

// §10.9.2: struct with three fields, named pattern
TEST(SimA60701, ThreeFieldStructNamedPattern) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] x;\n"
      "    logic [7:0] y;\n"
      "    logic [7:0] z;\n"
      "  } triple_t;\n"
      "  triple_t v;\n"
      "  initial begin\n"
      "    v = triple_t'{x: 8'd1, y: 8'd2, z: 8'd3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);
  // x=1 bits[23:16], y=2 bits[15:8], z=3 bits[7:0]: 0x010203 = 66051
  EXPECT_EQ(var->value.ToUint64(), 0x010203u);
}

// ---------------------------------------------------------------------------
// case-matches: constant pattern — simulation
// ---------------------------------------------------------------------------

// §12.6.1: case-matches selects matching constant pattern
TEST(SimA60701, CaseMatchesConstantMatch) {
  SimA60701Fixture f;
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

// §12.6.1: case-matches falls through to default
TEST(SimA60701, CaseMatchesDefaultFallthrough) {
  SimA60701Fixture f;
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

// §12.6.1: case-matches first match wins
TEST(SimA60701, CaseMatchesFirstMatchWins) {
  SimA60701Fixture f;
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

// ---------------------------------------------------------------------------
// matches operator in if-condition — simulation
// ---------------------------------------------------------------------------

// §12.6.2: matches with constant pattern — true case
TEST(SimA60701, MatchesConstantTrue) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.6.2: matches with constant pattern — false case
TEST(SimA60701, MatchesConstantFalse) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd10) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// assignment_pattern in procedural assignment — simulation
// ---------------------------------------------------------------------------

// §10.9: assignment pattern in blocking assignment
TEST(SimA60701, PatternInBlockingAssignment) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 11u);
  EXPECT_EQ(b->value.ToUint64(), 22u);
}

// §10.9: assignment pattern used in conditional branch
TEST(SimA60701, PatternInConditionalBranch) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    if (1) x = '{8'd5, 8'd6};\n"
      "    else x = '{8'd0, 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd5, 8'd6} = {8'h05, 8'h06} = 16'h0506 = 1286
  EXPECT_EQ(var->value.ToUint64(), 1286u);
}

// §10.9: assignment pattern used in case item body
TEST(SimA60701, PatternInCaseItemBody) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd0: x = '{8'd0, 8'd0};\n"
      "      8'd1: x = '{8'd10, 8'd20};\n"
      "      default: x = '{8'd0, 8'd0};\n"
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
  // '{8'd10, 8'd20} = {8'h0A, 8'h14} = 16'h0A14 = 2580
  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

// §10.9: assignment pattern in for loop body
TEST(SimA60701, PatternInForLoop) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = 16'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      x = '{8'd7, 8'd8};\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd7, 8'd8} = {8'h07, 8'h08} = 16'h0708 = 1800
  EXPECT_EQ(var->value.ToUint64(), 1800u);
}

// ---------------------------------------------------------------------------
// constant_assignment_pattern_expression — simulation
// ---------------------------------------------------------------------------

// §10.9: constant assignment pattern in variable declaration initializer
TEST(SimA60701, ConstPatternInVarDeclInit) {
  SimA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p = '{8'd100, 8'd200};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // '{8'd100, 8'd200} = {8'h64, 8'hC8} = 16'h64C8 = 25800
  EXPECT_EQ(var->value.ToUint64(), 25800u);
}
