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

TEST(FileAndLineMacroSimulation, LineExpandsToCorrectValue) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 3u);
}

TEST(FileAndLineMacroSimulation, LineValueDiffersPerLine) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  logic [31:0] dummy;\n"
      "  initial begin\n"
      "    dummy = `__LINE__;\n"
      "    result = `__LINE__;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 6u);
}
