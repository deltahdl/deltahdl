// §9.3.2: Parallel blocks

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

TEST(Lowerer, ForkJoinNone) {
  // fork/join_none: parent continues immediately.
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 10;\n"
      "      b = 20;\n"
      "    join_none\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *a = f.ctx.FindVariable("a");
  auto *b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 20u);
}

TEST(Lowerer, ForkJoin) {
  // fork/join: parent waits for all children to complete.
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b, done;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 10;\n"
      "      begin #2 b = 20; end\n"
      "    join\n"
      "    done = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  struct {
    const char *name;
    uint64_t expected;
  } const kCases[] = {{"a", 10u}, {"b", 20u}, {"done", 1u}};
  for (const auto &c : kCases) {
    auto *var = f.ctx.FindVariable(c.name);
    ASSERT_NE(var, nullptr);
    EXPECT_EQ(var->value.ToUint64(), c.expected);
  }
}

}  // namespace
