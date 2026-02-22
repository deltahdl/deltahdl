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

// §5.4 Comments

struct SimCh504Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh504Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string &src, const char *var_name) {
  SimCh504Fixture f;
  auto *design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design)
    return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var)
    return 0;
  return var->value.ToUint64();
}

// ---------------------------------------------------------------------------
// 1. Line comments stripped — simulation produces correct result
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentLineCommentStripped) {
  // §5.4: One-line comment starts with // and ends with newline.
  auto result = RunAndGet("module t; // module declaration\n"
                          "  logic [7:0] result; // variable\n"
                          "  initial result = 8'd77; // assignment\n"
                          "endmodule // end\n",
                          "result");
  EXPECT_EQ(result, 77u);
}

// ---------------------------------------------------------------------------
// 2. Block comments stripped — simulation produces correct result
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentBlockCommentStripped) {
  // §5.4: Block comment starts with /* and ends with */.
  auto result = RunAndGet(
      "module /* module */ t /* name */;\n"
      "  logic /* type */ [7:0] /* width */ result /* var */;\n"
      "  initial /* process */ result = /* assign */ 8'd55 /* val */;\n"
      "endmodule /* end */\n",
      "result");
  EXPECT_EQ(result, 55u);
}

// ---------------------------------------------------------------------------
// 3. Block comments not nested — first */ ends the comment
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentBlockNotNested) {
  // §5.4: Block comments are not nested.
  // "/* outer /* inner */" ends at first */ — remaining code is active.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial /* outer /* inner */ result = 8'd33;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 33u);
}

// ---------------------------------------------------------------------------
// 4. // inside block comment has no special meaning
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentLineInsideBlockNoEffect) {
  // §5.4: // has no special meaning inside a block comment.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  /* // this is not a line comment\n"
                          "     still inside block comment */\n"
                          "  initial result = 8'd99;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 99u);
}

// ---------------------------------------------------------------------------
// 5. /* and */ inside line comment have no special meaning
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentBlockInsideLineNoEffect) {
  // §5.4: /* and */ have no special meaning inside a one-line comment.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  // /* this does not start a block comment\n"
                          "  initial result = 8'd22;\n"
                          "  // */ this does not end a block comment\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 22u);
}

// ---------------------------------------------------------------------------
// 6. Mixed line and block comments in expressions
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentMixedInExpression) {
  // Both comment forms within an expression do not alter results.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] a, b, result;\n"
                          "  initial begin\n"
                          "    a = 8'd10; // ten\n"
                          "    b = /* twenty */ 8'd20;\n"
                          "    result = a /* plus */ + /* b */ b; // sum\n"
                          "  end\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 30u);
}

// ---------------------------------------------------------------------------
// 7. Multiline block comment spans code lines
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentMultilineBlockSpan) {
  // A block comment spanning multiple lines removes all enclosed text.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial begin\n"
                          "    /* This block comment\n"
                          "       spans multiple\n"
                          "       lines */\n"
                          "    result = 8'd11;\n"
                          "  end\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 11u);
}

// ---------------------------------------------------------------------------
// 8. Block comment as token separator in simulation
// ---------------------------------------------------------------------------
TEST(SimCh504, CommentBlockAsSeparator) {
  // §5.4: Block comments serve as token separators, just like whitespace.
  auto result =
      RunAndGet("module/**/t;logic/**/[7:0]/**/result;initial/**/result=8'd71;"
                "endmodule",
                "result");
  EXPECT_EQ(result, 71u);
}
