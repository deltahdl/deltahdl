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
