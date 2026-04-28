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

TEST(CompilerDirectiveSimulation, DirectiveCanBeOverridden) {
  auto result = PreprocessAndGet(
      "`define X 8'd10\n"
      "`define X 8'd20\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `X;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 20u);
}

TEST(CompilerDirectiveSimulation, DirectiveInConditionalBlockAffectsSimulation) {
  auto result = PreprocessAndGet(
      "`define FEATURE 1\n"
      "`ifdef FEATURE\n"
      "`define VAL 8'd42\n"
      "`else\n"
      "`define VAL 8'd0\n"
      "`endif\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CompilerDirectiveSimulation, DirectiveInCommentDoesNotAffectSimulation) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd42\n"
      "// `define VAL 8'd99\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CompilerDirectiveSimulation, MacroExpansionWithinDirectiveAffectsSimulation) {
  auto result = PreprocessAndGet(
      "`define INNER 8'd77\n"
      "`define OUTER `INNER\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `OUTER;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}
