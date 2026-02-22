// §9.2.3: Final procedures

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct LowerFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, LowerFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

TEST(Lowerer, FinalBlockExecutesAfterRun) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  final x = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // Before RunFinalBlocks, x should still have default value.
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);

  f.ctx.RunFinalBlocks();
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(Lowerer, FinalBlockNotScheduledAtTimeZero) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 10;\n"
      "  final x = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // After scheduler, initial ran (x=10) but final didn't.
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(Lowerer, FinalBlocksFIFOOrder) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  final x = 10;\n"
      "  final x = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Second final block overwrites first, so x == 20.
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

}  // namespace
