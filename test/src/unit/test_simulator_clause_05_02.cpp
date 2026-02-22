#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

// §5.2 Lexical tokens

struct SimCh502Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh502Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string &src, const char *var_name) {
  SimCh502Fixture f;
  auto *design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// ---------------------------------------------------------------------------
// 1. Free format layout — different arrangements produce same simulation
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenFreeFormatIdenticalResult) {
  // §5.2: Free format — compact vs spread layout yields same result.
  auto compact = RunAndGet(
      "module t;logic [7:0] result;initial result=8'd42;endmodule", "result");
  auto spread = RunAndGet(
      "module\nt\n;\nlogic\n[7:0]\nresult\n;\ninitial\nresult\n=\n8'd42\n;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(compact, spread);
  EXPECT_EQ(compact, 42u);
}

// ---------------------------------------------------------------------------
// 2. Comments do not affect simulation results
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenCommentsDoNotAffectSimulation) {
  // §5.2: Comments are tokens consumed during lexing; they must not affect
  // simulation behavior.
  auto result = RunAndGet(
      "module /* block */ t; // line\n"
      "  logic [7:0] /* type */ result /* name */;\n"
      "  initial /* proc */ begin\n"
      "    result /* lhs */ = /* rhs */ 8'd88 /* val */;\n"
      "  end // done\n"
      "endmodule /* eof */\n",
      "result");
  EXPECT_EQ(result, 88u);
}

// ---------------------------------------------------------------------------
// 3. All token categories participate correctly in simulation
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenAllCategoriesInSimulation) {
  // §5.2: Keywords, identifiers, operators, numbers all affect behavior.
  // Keywords: module, logic, initial, begin, end, endmodule, if, else
  // Identifiers: t, a, b, result
  // Operators: =, >, ?, :
  // Numbers: 8'd10, 8'd20
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    result = (a > b) ? a : b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 20u);
}

// ---------------------------------------------------------------------------
// 4. Expression spanning multiple lines (free format)
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenMultilineExpression) {
  // §5.2: Free format — a single expression can span multiple lines.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial\n"
      "    result\n"
      "      =\n"
      "        8'd3\n"
      "          +\n"
      "        8'd7\n"
      "      ;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

// ---------------------------------------------------------------------------
// 5. Multiple statements on one line (free format)
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenMultipleStatementsOneLine) {
  // §5.2: Free format — multiple statements on one line.
  SimCh502Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin a = 8'd1; b = 8'd2; c = a + b; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 3u);
}

// ---------------------------------------------------------------------------
// 6. Block comment acts as token separator in simulation context
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenBlockCommentAsSeparator) {
  // §5.2: Block comments separate tokens, so "module/**/t" is valid.
  auto result = RunAndGet(
      "module/**/t;logic/**/[7:0]/**/result;initial/**/result=8'd66;"
      "endmodule",
      "result");
  EXPECT_EQ(result, 66u);
}

// ---------------------------------------------------------------------------
// 7. Line comment terminates at newline, next line is normal code
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenLineCommentTerminatesAtNewline) {
  // §5.2+§5.4: Line comment ends at newline; code on next line executes.
  auto result = RunAndGet(
      "module t; // this is a comment\n"
      "  logic [7:0] result; // another comment\n"
      "  initial result = 8'd44; // value\n"
      "endmodule // end\n",
      "result");
  EXPECT_EQ(result, 44u);
}

// ---------------------------------------------------------------------------
// 8. Free format with always_comb
// ---------------------------------------------------------------------------
TEST(SimCh502, LexicalTokenFreeFormatAlwaysComb) {
  // §5.2: Free format applies to all constructs including always_comb.
  auto result = RunAndGet(
      "module t; logic [7:0] a, result;\n"
      "initial a = 8'd5;\n"
      "always_comb result\n=\na\n+\n8'd10\n;\nendmodule\n",
      "result");
  EXPECT_EQ(result, 15u);
}
