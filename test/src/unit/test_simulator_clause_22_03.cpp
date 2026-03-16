#include "fixture_simulator.h"
#include "preprocessor/preprocessor.h"
#include "simulator/lowerer.h"
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

TEST(ResetAllSimulation, PreservesMacroValuesForSimulation) {
  auto result = PreprocessAndGet(
      "`define CONST 8'd77\n"
      "`resetall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `CONST;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(ResetAllSimulation, BetweenModulesResetsStateForSimulation) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd33\n"
      "module m1; endmodule\n"
      "`resetall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

TEST(ResetAllSimulation, InsideExcludedBranchDoesNotAffectSimulation) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd50\n"
      "`ifdef UNDEF\n"
      "`resetall\n"
      "`endif\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 50u);
}

TEST(ResetAllSimulation, MultipleResetallDoesNotAffectMacroSimulation) {
  auto result = PreprocessAndGet(
      "`define X 8'd12\n"
      "`resetall\n"
      "`resetall\n"
      "`resetall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `X;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}
