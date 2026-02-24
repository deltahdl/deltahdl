// §12.8.2

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

struct SimA608Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA608Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// §12.7.4: while with continue
TEST(SimA608, WhileContinue) {
  SimA608Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    while (x < 8'd6) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // 6 iterations (x = 1..6), skip x==3 => count = 5
  EXPECT_EQ(count->value.ToUint64(), 5u);
}

}  // namespace
