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

TEST(TimescaleSimulation, TimescaleModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(TimescaleSimulation, MultipleTimescaleModulesSimulate) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "module m1;\n"
      "  logic [7:0] unused;\n"
      "  initial unused = 8'd10;\n"
      "endmodule\n"
      "`timescale 1us / 1ns\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd77;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(TimescaleSimulation, LaterTimescaleOverrideSimulates) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "`timescale 10us / 1us\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}
