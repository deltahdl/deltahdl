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

// §5.6.2 Keywords

struct SimCh50602Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh50602Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh50602Fixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

TEST(SimCh50602, KeywordDefinesConstruct) {
  // §5.6.2: Keywords define language constructs (if/else/begin/end/for).
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    for (int i = 0; i < 5; i++) result = result + 8'd1;\n"
      "    if (result == 8'd5) result = result + 8'd10;\n"
      "    else result = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 15u);
}

TEST(SimCh50602, EscapedKeywordCoexistsWithKeyword) {
  // §5.6.2: Escaped keyword (\begin) used as variable inside begin/end block.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\begin ;\n"
      "  initial begin\n"
      "    \\begin = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "\\begin");
  EXPECT_EQ(result, 42u);
}

TEST(SimCh50602, KeywordLowercaseOnly) {
  // §5.6.2: Keywords are lowercase only; uppercase is an identifier.
  SimCh50602Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] Initial, result;\n"
      "  initial begin\n"
      "    Initial = 8'd7;\n"
      "    result = Initial + 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}
