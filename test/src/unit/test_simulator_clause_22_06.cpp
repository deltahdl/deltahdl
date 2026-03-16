#include "fixture_simulator.h"
#include "preprocessor/preprocessor.h"
#include "simulator/variable.h"

using namespace delta;

static uint64_t PreprocessAndGet(const std::string& src, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  auto preprocessed = pp.Preprocess(fid);
  auto fid2 = f.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f.mgr.FileContent(fid2), fid2, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
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

TEST(IfdefSimulation, IfdefSelectsValueForSimulation) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd77;\n"
      "`else\n"
      "  initial result = 8'd11;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(IfdefSimulation, IfdefElseBranchSimulatesWhenUndefined) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd77;\n"
      "`else\n"
      "  initial result = 8'd11;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 11u);
}

TEST(IfdefSimulation, ElsifChainSelectsCorrectValueForSimulation) {
  auto result = PreprocessAndGet(
      "`define MODE_C\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef MODE_A\n"
      "  initial result = 8'd1;\n"
      "`elsif MODE_B\n"
      "  initial result = 8'd2;\n"
      "`elsif MODE_C\n"
      "  initial result = 8'd3;\n"
      "`else\n"
      "  initial result = 8'd4;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 3u);
}

TEST(IfdefSimulation, IfndefSimulatesWhenUndefined) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifndef MISSING\n"
      "  initial result = 8'd55;\n"
      "`else\n"
      "  initial result = 8'd0;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}
