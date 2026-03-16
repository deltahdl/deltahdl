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

TEST(DefineSimulation, ObjectLikeMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd99\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(DefineSimulation, FunctionLikeMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define DOUBLE(x) (x * 2)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `DOUBLE(8'd7);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 14u);
}

TEST(DefineSimulation, RedefinedMacroUsesLatestValueForSimulation) {
  auto result = PreprocessAndGet(
      "`define V 8'd10\n"
      "`define V 8'd25\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `V;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 25u);
}

TEST(DefineSimulation, NestedMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define INNER 8'd4\n"
      "`define OUTER (`INNER + 8'd6)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `OUTER;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

TEST(DefineSimulation, MacroWithDefaultArgSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define ADD(a, b=8'd50) (a + b)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `ADD(8'd3);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 53u);
}
