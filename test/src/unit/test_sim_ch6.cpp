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

// §6.23: type(expr) in variable declaration resolves type.
TEST(SimCh6, TypeRefVarDecl) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    b = 100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  // type(a) = int → 32-bit width
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 100u);
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

// §6.24.2: $cast function form returns 1 on valid enum cast.
TEST(SimCh6, CastEnumSuccess) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = $cast(c, 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
}

// §6.24.2: $cast function form returns 0 on invalid enum cast.
TEST(SimCh6, CastEnumFailure) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = $cast(c, 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 0u);
  // c should remain unchanged (default 0).
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 0u);
}

// §6.24.3: Bit-stream cast packs unpacked array elements MSB-first.
TEST(SimCh6, BitStreamArrayToInt) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hDE;\n"
      "    arr[1] = 8'hAD;\n"
      "    arr[2] = 8'hBE;\n"
      "    arr[3] = 8'hEF;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // §6.24.3: index 0 occupies MSBs → 0xDEADBEEF.
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// §6.24.3: Bit-stream cast packs shortint array into 32-bit int.
TEST(SimCh6, BitStreamShortArrayToInt) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 16'hCAFE;\n"
      "    arr[1] = 16'hBABE;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 0xCAFE at MSBs, 0xBABE at LSBs → 0xCAFEBABE.
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEBABEu);
}

static void VerifyNetByName(const RtlirModule* mod, std::string_view name,
                            uint32_t expected_width, bool& found) {
  for (const auto& n : mod->nets) {
    if (n.name == name) {
      found = true;
      EXPECT_EQ(n.width, expected_width);
    }
  }
}

// §6.6.7: User-defined nettype creates a net with correct width.
TEST(SimCh6, NettypeCreatesNet) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] byte_net;\n"
      "  byte_net x;\n"
      "  assign x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  // Check RTLIR: x should be in mod->nets, not mod->variables.
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  bool found_net = false;
  VerifyNetByName(mod, "x", 8u, found_net);
  EXPECT_TRUE(found_net) << "x should be elaborated as a net, not a variable";

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("x");
  ASSERT_NE(net, nullptr);
}

// §6.6.7: Nettype with 16-bit type creates correctly-sized net.
TEST(SimCh6, NettypeWideNet) {
  SimCh6Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [15:0] wide_net;\n"
      "  wide_net y;\n"
      "  assign y = 16'hBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  bool found_net = false;
  VerifyNetByName(mod, "y", 16u, found_net);
  EXPECT_TRUE(found_net) << "y should be elaborated as a net";
}
