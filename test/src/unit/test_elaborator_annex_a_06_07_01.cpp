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

}  // namespace

// =============================================================================
// A.6.7.1 Patterns — Elaboration tests
// =============================================================================

// §10.9: positional assignment pattern elaborates for struct init
TEST(ElabA60701, StructPositionalPatternElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd10, 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.9: named assignment pattern elaborates for struct init
TEST(ElabA60701, StructNamedPatternElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd1, b: 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.9: assignment pattern with default key elaborates
TEST(ElabA60701, PatternDefaultKeyElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{default: 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

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

// §12.6: case-matches statement elaborates
TEST(ElabA60701, CaseMatchesElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §12.6.2: matches operator in if-condition elaborates
TEST(ElabA60701, MatchesInIfElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    if (x matches 8'd3) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}
