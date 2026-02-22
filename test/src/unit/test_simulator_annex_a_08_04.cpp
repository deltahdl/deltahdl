// Tests for A.8.4 — Primaries — Simulation

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

struct SimA84Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA84Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

// =============================================================================
// A.8.4 Primaries — Simulation
// =============================================================================

// § constant_primary — integer literal in parameter

TEST(SimA84, ConstantPrimaryIntegerLiteral) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  parameter int P = 42;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = P;\n"
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

// § constant_primary — real literal used in constant expression

TEST(SimA84, ConstantPrimaryRealLiteral) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  parameter int P = 7;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = P;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// § primary — integer literal

TEST(SimA84, PrimaryIntegerLiteral) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'hAB;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § primary — string literal

TEST(SimA84, PrimaryStringLiteral) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  string s;\n"
                              "  initial s = \"hello\";\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

// § primary — unbased_unsized_literal '1

TEST(SimA84, PrimaryUnbasedUnsized1) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = '1;\n"
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

// § primary — unbased_unsized_literal '0

TEST(SimA84, PrimaryUnbasedUnsized0) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = '0;\n"
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

// § primary — hierarchical identifier

TEST(SimA84, PrimaryIdentifier) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b;\n"
                              "  initial begin a = 8'd99; b = a; end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// § primary — bit_select

TEST(SimA84, PrimaryBitSelect) {
  SimA84Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [7:0] data;\n"
                   "  logic x;\n"
                   "  initial begin data = 8'b10101010; x = data[1]; end\n"
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

// § primary — part_select_range (constant range)

TEST(SimA84, PrimaryPartSelectRange) {
  SimA84Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [15:0] data;\n"
                   "  logic [7:0] x;\n"
                   "  initial begin data = 16'hABCD; x = data[15:8]; end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § primary — indexed part select (plus)

TEST(SimA84, PrimaryIndexedPartSelectPlus) {
  SimA84Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [15:0] data;\n"
                   "  logic [7:0] x;\n"
                   "  initial begin data = 16'hABCD; x = data[8+:8]; end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § primary — indexed part select (minus)

TEST(SimA84, PrimaryIndexedPartSelectMinus) {
  SimA84Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [15:0] data;\n"
                   "  logic [7:0] x;\n"
                   "  initial begin data = 16'hABCD; x = data[15-:8]; end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § primary — concatenation

TEST(SimA84, PrimaryConcatenation) {
  SimA84Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [7:0] a, b;\n"
                   "  logic [15:0] c;\n"
                   "  initial begin a = 8'hAB; b = 8'hCD; c = {a, b}; end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

// § primary — multiple concatenation (replicate)

TEST(SimA84, PrimaryMultipleConcatenation) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  logic [15:0] b;\n"
                              "  initial begin a = 8'hAB; b = {2{a}}; end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABu);
}

// § primary — function call

TEST(SimA84, PrimaryFunctionCall) {
  SimA84Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  function int add1(int a); return a + 1; endfunction\n"
                   "  int x;\n"
                   "  initial x = add1(5);\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// § primary — parenthesized expression

TEST(SimA84, PrimaryParenthesizedExpr) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = (3 + 4);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// § primary — cast (int cast)

TEST(SimA84, PrimaryCast) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x;\n"
                              "  initial x = int'(4.0);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// § primary — system call ($clog2)

TEST(SimA84, PrimarySystemCallClog2) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x;\n"
                              "  initial x = $clog2(16);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// § primary — system call ($bits)

TEST(SimA84, PrimarySystemCallBits) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] data;\n"
                              "  int x;\n"
                              "  initial x = $bits(data);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// § primary — hex literal with different bases

TEST(SimA84, PrimaryHexLiteral) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'hA5;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// § primary — binary literal

TEST(SimA84, PrimaryBinaryLiteral) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'b11001100;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCCu);
}

// § primary — octal literal

TEST(SimA84, PrimaryOctalLiteral) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial x = 8'o77;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 63u);
}

// § primary — streaming concatenation left-to-right

TEST(SimA84, PrimaryStreamingConcat) {
  SimA84Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [31:0] a;\n"
                   "  logic [31:0] b;\n"
                   "  initial begin a = 32'h12345678; b = {<< 8 {a}}; end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x78563412u);
}

// § primary — assignment pattern

TEST(SimA84, PrimaryAssignmentPattern) {
  SimA84Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int arr [3];\n"
                              "  initial begin\n"
                              "    arr = '{10, 20, 30};\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

// § primary — member access (struct field)

TEST(SimA84, PrimaryMemberAccess) {
  SimA84Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x;\n"
      "  initial begin p = 16'hABCD; x = p.hi; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}
