// Tests for A.8.1 — Concatenations — Simulation

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

struct SimA81Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA81Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.8.1 Concatenations — Simulation
// =============================================================================

// § concatenation — two elements evaluated correctly

TEST(SimA81, ConcatenationTwoElements) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {4'hA, 4'h5};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// § concatenation — three elements

TEST(SimA81, ConcatenationThreeElements) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] result;\n"
      "  initial result = {4'hF, 4'h0, 4'hA};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0Au);
}

// § concatenation — nested

TEST(SimA81, ConcatenationNested) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] result;\n"
      "  initial result = {4'hA, {4'hB, 4'hC}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

// § multiple_concatenation (replication)

TEST(SimA81, ReplicationBasic) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {2{4'hA}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(SimA81, ReplicationFour) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {4{2'b10}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 2'b10 replicated 4 times = 8'b10101010 = 0xAA
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

// § multiple_concatenation with multiple inner elements

TEST(SimA81, ReplicationMultipleInner) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = {2{4'hA, 4'h5}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // {A,5} replicated 2 times = A5A5
  EXPECT_EQ(var->value.ToUint64(), 0xA5A5u);
}

// § streaming_concatenation — right-shift (no reversal)

TEST(SimA81, StreamingRightShift) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § streaming_concatenation — left-shift (bit reversal)

TEST(SimA81, StreamingLeftShift) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 0xAB = 10101011 reversed = 11010101 = 0xD5
  EXPECT_EQ(var->value.ToUint64(), 0xD5u);
}

// § streaming_concatenation — multiple stream elements

TEST(SimA81, StreamingMultipleElements) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {4'hA, 4'h5}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// § concatenation with variables

TEST(SimA81, ConcatWithVariables) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hC;\n"
      "    b = 4'h3;\n"
      "    result = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xC3u);
}

// § concatenation as LHS (unpacking)

TEST(SimA81, ConcatAsLHS) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hC3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *va = f.ctx.FindVariable("a");
  auto *vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xCu);
  EXPECT_EQ(vb->value.ToUint64(), 0x3u);
}

// § concatenation — does not interfere with other initial blocks

TEST(SimA81, ConcatDoesNotInterfere) {
  SimA81Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {4'h1, 4'h2};\n"
      "  initial b = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *va = f.ctx.FindVariable("a");
  auto *vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0x12u);
  EXPECT_EQ(vb->value.ToUint64(), 99u);
}
