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

// §5.6.3 System tasks and system functions

struct SimCh50603Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh50603Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string &src, const char *var_name) {
  SimCh50603Fixture f;
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

TEST(SimCh50603, SystemTaskDoesNotConsumeTime) {
  // §5.6.3: Standard system tasks do not consume simulation time.
  // $display executes at time 0; result assigned after it proves no time
  // passes.
  SimCh50603Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] result;\n"
                              "  initial begin\n"
                              "    result = 8'd1;\n"
                              "    $display(\"msg\");\n"
                              "    result = result + 8'd2;\n"
                              "    $display(\"msg2\");\n"
                              "    result = result + 8'd4;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // All three assignments complete without any time advancement.
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(SimCh50603, SystemFunctionReturnsValue) {
  // §5.6.3: A name following $ is a system function; it returns a value.
  // $clog2 is a standard system function (§20.6).
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = $clog2(256);\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 8u);
}

TEST(SimCh50603, SystemFunctionInExpression) {
  // §5.6.3: System functions can be used in expressions like void functions.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = $clog2(32) + $clog2(16);\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 9u); // 5 + 4
}
