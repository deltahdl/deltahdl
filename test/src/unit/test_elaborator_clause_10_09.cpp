// §10.9: Assignment patterns

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

struct ElabA60701Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA60701Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// §10.9: typed assignment pattern expression elaborates
TEST(ElabA60701, TypedPatternExpressionElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } coord_t;\n"
      "  coord_t c;\n"
      "  initial begin\n"
      "    c = coord_t'{x: 8'd5, y: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
