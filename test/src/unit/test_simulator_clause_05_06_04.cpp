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

TEST(CompilerDirectiveIdentSim, DefineMacroAffectsSimulation) {
  auto result = PreprocessAndGet(
      "`define MY_VAL 8'd42\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `MY_VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

// §5.6.4: "The directive shall remain in effect for the rest of the
// compilation unit ... unless a different compiler directive specifies
// otherwise."  A `define before an intervening module remains visible in
// a later module of the same compilation unit, end-to-end through the
// simulator.
TEST(CompilerDirectiveSimulation, DirectivePersistsInCompilationUnit) {
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

// §5.6.4: "...unless a different compiler directive specifies otherwise."
// A later `define overrides an earlier one before simulation observes the
// macro's expanded value.
TEST(CompilerDirectiveSimulation, DirectiveOverriddenBeforeSimulation) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd11\n"
      "`define VAL 8'd55\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}

// §5.6.4: "A compiler directive shall not affect other compilation units."
// Each PreprocessAndGet invocation builds its own Preprocessor (i.e., its
// own compilation unit); a `define from a prior simulation cannot leak
// into a later one.  The second simulation must fail to elaborate because
// the macro is undefined in its CU.
TEST(CompilerDirectiveSimulation, MacroDoesNotLeakBetweenCus) {
  // CU1: define and use the macro, simulate normally.
  auto first = PreprocessAndGet(
      "`define LEAK 8'd17\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `LEAK;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(first, 17u);

  // CU2: fresh fixture, fresh Preprocessor.  Reference the same macro
  // without redefining it — preprocessing leaves `LEAK in the source,
  // which the lexer rejects, leaving a missing variable in the simulator.
  SimFixture f2;
  auto fid = f2.mgr.AddFile(
      "<test>",
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `LEAK;\n"
      "endmodule\n");
  Preprocessor pp2(f2.mgr, f2.diag, {});
  auto preprocessed = pp2.Preprocess(fid);
  auto fid2 = f2.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f2.mgr.FileContent(fid2), fid2, f2.diag);
  Parser parser(lexer, f2.arena, f2.diag);
  parser.Parse();
  EXPECT_TRUE(f2.diag.HasErrors());
}
