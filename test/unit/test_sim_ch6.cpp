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
