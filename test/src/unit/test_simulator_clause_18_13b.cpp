// §18.13: Random number system functions and methods

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
#include <gtest/gtest.h>

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

TEST(Lowerer, UrandomReturnsValue) {
  LowerFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] x;\n"
                              "  initial x = $urandom;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Seed 0 is deterministic; just verify it ran without crash.
  EXPECT_NE(var->value.ToUint64(), 0u);
}

} // namespace
