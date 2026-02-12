#include <gtest/gtest.h>

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

struct SimCh6Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh6Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// §6.24.1: signed'(x) sets is_signed flag.
TEST(SimCh6, CastSigned) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 8'hFF;\n"
      "    result = signed'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 8'hFF sign-extended to 32 bits = 0xFFFFFFFF (-1 as unsigned).
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// §6.24.1: unsigned'(x) clears is_signed flag.
TEST(SimCh6, CastUnsigned) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = -1;\n"
      "    result = unsigned'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // unsigned'(-1) on 32-bit = 0xFFFFFFFF.
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// §6.24.1: shortint'(x) casts to 16-bit width.
TEST(SimCh6, CastShortint) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = 32'h1234ABCD;\n"
      "    result = shortint'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // shortint'(32'h1234ABCD) truncates to 16 bits = 0xABCD.
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

// §6.20.3: Type parameter with default type resolves variable width.
TEST(SimCh6, TypeParameterDefault) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter type T = shortint;\n"
      "  T x;\n"
      "  initial x = 32'hFFFFFFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // T = shortint (16-bit), so x truncates to 16 bits.
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

// §6.12.1: real→int cast rounds to nearest, ties away from zero.
TEST(SimCh6, CastRealToInt_RoundUp) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 2.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 2.5 rounds to 3 (ties away from zero).
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §6.12.1: real→int cast rounds negative half away from zero.
TEST(SimCh6, CastRealToInt_NegRound) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = -1.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // -1.5 rounds to -2 (ties away from zero). As uint64: 0xFFFFFFFE.
  auto neg2_32bit = static_cast<uint32_t>(-2);
  EXPECT_EQ(var->value.ToUint64(), neg2_32bit);
}

// §6.12.1: real→int cast truncates fractional part toward zero.
TEST(SimCh6, CastRealToInt_Truncate) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 2.4;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 2.4 rounds to 2.
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §6.20.7: $isunbounded returns 1 for parameter with $ value.
TEST(SimCh6, IsunboundedTrue) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int p = $;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §6.20.7: $isunbounded returns 0 for parameter with numeric value.
TEST(SimCh6, IsunboundedFalse) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int p = 42;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}
