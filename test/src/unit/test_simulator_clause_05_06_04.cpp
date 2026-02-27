
#include "preprocessor/preprocessor.h"
#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

// §5.6.4 Compiler directives

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

TEST(SimCh50604, DefineMacroAffectsSimulation) {
  // §5.6.4: ` introduces a compiler directive (`define) that takes effect
  // immediately, expanding the macro during compilation.
  auto result = PreprocessAndGet(
      "`define MY_VAL 8'd42\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `MY_VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(SimCh50604, DirectivePersistsInCompilationUnit) {
  // §5.6.4: A directive remains in effect for the rest of the compilation
  // unit unless a different compiler directive specifies otherwise.
  auto result = PreprocessAndGet(
      "`define CONST 8'd99\n"
      "module other; endmodule\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `CONST;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(SimCh50604, DirectiveCanBeOverridden) {
  // §5.6.4: A directive can be overridden by a later directive.
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
