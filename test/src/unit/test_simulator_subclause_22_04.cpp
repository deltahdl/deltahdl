#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_include_test_dir.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

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

static uint64_t RunWithPiece(const std::string& piece,
                             const std::string& main_src) {
  IncludeTestDir tmp;
  tmp.WriteFile("piece.svh", piece);
  return PreprocessAndGet(tmp, main_src, "result");
}

TEST(IncludeFileSimulation, IncludedInsideAPackageBody) {
  EXPECT_EQ(RunWithPiece("parameter int P = 7;\n",
                         "package pk;\n"
                         "`include \"piece.svh\"\n"
                         "endpackage\n"
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  initial result = pk::P;\n"
                         "endmodule\n"),
            7u);
}

TEST(IncludeFileSimulation, IncludedInsideAClassBody) {
  EXPECT_EQ(RunWithPiece("int v = 8;\n",
                         "class c;\n"
                         "`include \"piece.svh\"\n"
                         "endclass\n"
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  c o;\n"
                         "  initial begin\n"
                         "    o = new;\n"
                         "    result = o.v;\n"
                         "  end\n"
                         "endmodule\n"),
            8u);
}

TEST(IncludeFileSimulation, IncludedInsideAnInterfaceBody) {
  EXPECT_EQ(RunWithPiece("logic [7:0] w = 8'd9;\n",
                         "interface ifc;\n"
                         "`include \"piece.svh\"\n"
                         "endinterface\n"
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  ifc i();\n"
                         "  initial #1 result = i.w;\n"
                         "endmodule\n"),
            9u);
}

TEST(IncludeFileSimulation, IncludedInsideAProgramBody) {
  EXPECT_EQ(RunWithPiece("initial o = 8'd11;\n",
                         "program p(output logic [7:0] o);\n"
                         "`include \"piece.svh\"\n"
                         "endprogram\n"
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  p pi(result);\n"
                         "endmodule\n"),
            11u);
}

TEST(IncludeFileSimulation, IncludedInsideAFunctionBody) {
  EXPECT_EQ(RunWithPiece("return 12;\n",
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  function automatic int f();\n"
                         "`include \"piece.svh\"\n"
                         "  endfunction\n"
                         "  initial result = f();\n"
                         "endmodule\n"),
            12u);
}

TEST(IncludeFileSimulation, IncludedAmongATasksStatements) {
  EXPECT_EQ(RunWithPiece("o = 8'd13;\n",
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  task automatic tk(output logic [7:0] o);\n"
                         "`include \"piece.svh\"\n"
                         "  endtask\n"
                         "  initial tk(result);\n"
                         "endmodule\n"),
            13u);
}

TEST(IncludeFileSimulation, IncludedInsideAGenerateBlock) {
  EXPECT_EQ(RunWithPiece("logic [7:0] gv = 8'd14;\n",
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  if (1) begin : g\n"
                         "`include \"piece.svh\"\n"
                         "  end\n"
                         "  initial #1 result = g.gv;\n"
                         "endmodule\n"),
            14u);
}

TEST(IncludeFileSimulation, IncludedAsAStatementOfAnInitialBlock) {
  EXPECT_EQ(RunWithPiece("result = 8'd15;\n",
                         "module t;\n"
                         "  logic [7:0] result;\n"
                         "  initial begin\n"
                         "`include \"piece.svh\"\n"
                         "  end\n"
                         "endmodule\n"),
            15u);
}
