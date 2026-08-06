#include "helpers_include_test_dir.h"
#include "helpers_preprocess_and_get.h"

static uint64_t PreprocessAndGet(IncludeTestDir& tmp,
                                 const std::string& main_src,
                                 const char* var_name) {
  SimFixture f;
  tmp.WriteFile("main.sv", main_src);
  auto fid = f.mgr.AddFile((tmp.dir / "main.sv").string(), main_src);
  Preprocessor pp(f.mgr, f.diag, {});
  return RunPreprocessedSim(f, fid, var_name, pp);
}

TEST(IncludeFileSimulation, IncludedMacroValueSimulatesCorrectly) {
  IncludeTestDir tmp;
  tmp.WriteFile("constants.svh", "`define MAGIC 8'd42\n");

  auto result = PreprocessAndGet(tmp,
                                 "`include \"constants.svh\"\n"
                                 "module t;\n"
                                 "  logic [7:0] result;\n"
                                 "  initial result = `MAGIC;\n"
                                 "endmodule\n",
                                 "result");
  EXPECT_EQ(result, 42u);
}

TEST(IncludeFileSimulation, NestedIncludeMacroSimulatesCorrectly) {
  IncludeTestDir tmp;
  tmp.WriteFile("base.svh", "`define BASE 8'd10\n");
  tmp.WriteFile("derived.svh",
                "`include \"base.svh\"\n"
                "`define DERIVED (`BASE + 8'd5)\n");

  auto result = PreprocessAndGet(tmp,
                                 "`include \"derived.svh\"\n"
                                 "module t;\n"
                                 "  logic [7:0] result;\n"
                                 "  initial result = `DERIVED;\n"
                                 "endmodule\n",
                                 "result");
  EXPECT_EQ(result, 15u);
}

TEST(IncludeFileSimulation, MultipleIncludesContributeToSimulation) {
  IncludeTestDir tmp;
  tmp.WriteFile("val_a.svh", "`define A 8'd3\n");
  tmp.WriteFile("val_b.svh", "`define B 8'd7\n");

  auto result = PreprocessAndGet(tmp,
                                 "`include \"val_a.svh\"\n"
                                 "`include \"val_b.svh\"\n"
                                 "module t;\n"
                                 "  logic [7:0] result;\n"
                                 "  initial result = `A + `B;\n"
                                 "endmodule\n",
                                 "result");
  EXPECT_EQ(result, 10u);
}

// §22.4 end-to-end via the §22.5.1 dependency: the include argument is produced
// by a text macro. The directive determines its filename from the expanded
// macro text, so the file is inserted and the value it defines is observable at
// simulation. Exercises the macro-expanded-filename path through the full
// preprocess -> parse -> elaborate -> run pipeline, not just preprocessor
// output.
TEST(IncludeFileSimulation, IncludeFilenameFromMacroSimulates) {
  IncludeTestDir tmp;
  tmp.WriteFile("payload.svh", "`define VAL 8'd55\n");

  auto result = PreprocessAndGet(tmp,
                                 "`define HDR \"payload.svh\"\n"
                                 "`include `HDR\n"
                                 "module t;\n"
                                 "  logic [7:0] result;\n"
                                 "  initial result = `VAL;\n"
                                 "endmodule\n",
                                 "result");
  EXPECT_EQ(result, 55u);
}

// §22.4 end-to-end via the §22.6 dependency: an include nested in a conditional
// compilation block is processed only when its branch is active. The taken
// branch's file is inserted (and the other branch's file is not), so the value
// observed at simulation discriminates which include the conditional selected.
TEST(IncludeFileSimulation, ConditionalIncludeSelectsActiveBranch) {
  IncludeTestDir tmp;
  tmp.WriteFile("high.svh", "`define SEL 8'd200\n");
  tmp.WriteFile("low.svh", "`define SEL 8'd1\n");

  auto result = PreprocessAndGet(tmp,
                                 "`define USE_HIGH\n"
                                 "`ifdef USE_HIGH\n"
                                 "`include \"high.svh\"\n"
                                 "`else\n"
                                 "`include \"low.svh\"\n"
                                 "`endif\n"
                                 "module t;\n"
                                 "  logic [7:0] result;\n"
                                 "  initial result = `SEL;\n"
                                 "endmodule\n",
                                 "result");
  EXPECT_EQ(result, 200u);
}
