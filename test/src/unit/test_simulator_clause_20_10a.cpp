// §20.10: Severity system tasks

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

TEST(Lowerer, FatalStopsSim) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    $fatal(1, \"test fatal\");\n"
      "    x = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_TRUE(f.ctx.StopRequested());
}

TEST(Lowerer, ErrorDoesNotStop) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    $error(\"test error\");\n"
      "    x = 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_FALSE(f.ctx.StopRequested());
}

TEST(Lowerer, WarningContinues) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    $warning(\"test warning\");\n"
      "    x = 7;\n"
      "  end\n"
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

}  // namespace
