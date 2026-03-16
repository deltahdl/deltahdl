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

TEST(PragmaSimulation, PragmaInsideModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  `pragma some_pragma\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(PragmaSimulation, PragmaBetweenModulesSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "module m1;\n"
      "  logic [7:0] unused;\n"
      "  initial unused = 8'd10;\n"
      "endmodule\n"
      "`pragma some_pragma key = val\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd55;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}

TEST(PragmaSimulation, MultiplePragmasSimulate) {
  auto result = PreprocessAndGet(
      "`pragma first_pragma\n"
      "module t;\n"
      "  `pragma second_pragma 42\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd77;\n"
      "endmodule\n"
      "`pragma third_pragma\n",
      "result");
  EXPECT_EQ(result, 77u);
}
