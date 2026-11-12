#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ConstantFunctionSim, Clogb2ResultReachesRuntime) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function integer clogb2(input int value);\n"
      "    value = value - 1;\n"
      "    for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)\n"
      "      value = value >> 1;\n"
      "  endfunction\n"
      "  localparam addr_width = clogb2(256);\n"
      "  initial $display(\"%0d\", addr_width);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8\n");
}

TEST(ConstantFunctionSim, FoldedValueSizesRuntimeSignal) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int double_val(int n); return n * 2; endfunction\n"
      "  localparam int P = double_val(4);\n"
      "  logic [P-1:0] bus;\n"
      "  initial $display(\"%0d %0d\", P, $bits(bus));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8 8\n");
}

TEST(ConstantFunctionSim, ConstFunctionCallInPackedDimension) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  logic [calc(3)-1:0] bus;\n"
      "  initial $display(\"%0d\", $bits(bus));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "6\n");
}

TEST(ConstantFunctionSim, SystemTaskInBodyProducesNoOutput) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int compute(int n);\n"
      "    $write(\"SIDEEFFECT\");\n"
      "    return n * 2;\n"
      "  endfunction\n"
      "  localparam int P = compute(4);\n"
      "  initial $display(\"%0d\", P);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8\n");
}

TEST(ConstantFunctionSim,
     DISABLED_AStaticClassMethodCallSizesARangeAndDecidesAGenerate) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C;\n"
                 "  static function int f(int a); return a * 2; endfunction\n"
                 "endclass\n"
                 "module m;\n"
                 "  logic [C::f(2)-1:0] x;\n"
                 "  int arr [C::f(3)];\n"
                 "  if (C::f(1) == 2) begin : g int z = 7; end\n"
                 "  else begin : g int z = 8; end\n"
                 "  for (genvar i = 0; i < C::f(2); i++) begin : lp\n"
                 "    int z = i;\n"
                 "  end\n"
                 "  initial $display(\"%0d %0d %0d %0d\",\n"
                 "      $bits(x), $size(arr), g.z, lp[3].z);\n"
                 "endmodule\n",
                 f),
      "4 6 7 3\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim,
     DISABLED_APackageParameterReadByAConstantFunctionSizesARange) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  parameter int P = 5;\n"
                 "endpackage\n"
                 "package pq;\n"
                 "  parameter int Q = 3;\n"
                 "  function automatic int qf(); return pk::P + Q; "
                 "endfunction\n"
                 "endpackage\n"
                 "function automatic int uf(); return pk::P * 2; endfunction\n"
                 "class K;\n"
                 "  static function int kf(); return pk::P + 1; endfunction\n"
                 "endclass\n"
                 "interface ifc;\n"
                 "  function automatic int itf(); return pk::P + 2; "
                 "endfunction\n"
                 "  logic [itf()-1:0] v;\n"
                 "endinterface\n"
                 "program prg;\n"
                 "  function automatic int pf(); return pk::P + 4; "
                 "endfunction\n"
                 "  logic [pf()-1:0] v;\n"
                 "  initial $display(\"%0d\", $bits(v));\n"
                 "endprogram\n"
                 "module m;\n"
                 "  function automatic int mf(); return pk::P; endfunction\n"
                 "  logic [mf()-1:0] a;\n"
                 "  logic [pq::qf()-1:0] b;\n"
                 "  logic [uf()-1:0] c;\n"
                 "  logic [K::kf()-1:0] d;\n"
                 "  ifc i();\n"
                 "  prg p();\n"
                 "  if (mf() == 5) begin : g int z = 1; end\n"
                 "  else begin : g int z = 2; end\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d\",\n"
                 "      $bits(a), $bits(b), $bits(c), $bits(d), $bits(i.v), "
                 "g.z);\n"
                 "endmodule\n",
                 f),
      "5 8 10 6 7 1\n9\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim, DISABLED_AStringMethodFoldsInEveryContextAndScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  function automatic int pl(string s); return s.len(); "
                 "endfunction\n"
                 "endpackage\n"
                 "function automatic int ul(string s); return s.len() + 1;\n"
                 "endfunction\n"
                 "interface ifc;\n"
                 "  function automatic int il(string s); return s.len() + 2;\n"
                 "  endfunction\n"
                 "  logic [il(\"ab\")-1:0] v;\n"
                 "endinterface\n"
                 "program prg;\n"
                 "  function automatic int prl(string s); return s.len() + 4;\n"
                 "  endfunction\n"
                 "  logic [prl(\"ab\")-1:0] v;\n"
                 "  initial $display(\"%0d\", $bits(v));\n"
                 "endprogram\n"
                 "module m;\n"
                 "  function automatic int ml(string s); return s.len(); "
                 "endfunction\n"
                 "  localparam int L = ml(\"abcde\");\n"
                 "  logic [ml(\"abc\")-1:0] a;\n"
                 "  logic [pk::pl(\"abcd\")-1:0] b;\n"
                 "  logic [ul(\"ab\")-1:0] c;\n"
                 "  ifc i();\n"
                 "  prg p();\n"
                 "  if (ml(\"ab\") == 2) begin : g int z = 1; end\n"
                 "  else begin : g int z = 2; end\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d\",\n"
                 "      L, $bits(a), $bits(b), $bits(c), $bits(i.v), g.z);\n"
                 "endmodule\n",
                 f),
      "5 3 4 3 4 1\n6\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim,
     AConstantCallLeavesAStaticFunctionsLocalAtItsDefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  function int f(int k); int c; c = c + k; return c;\n"
                       "  endfunction\n"
                       "  localparam int P = f(1);\n"
                       "  localparam int Q = f(1);\n"
                       "  logic [Q-1:0] x;\n"
                       "  initial begin\n"
                       "    $display(\"%0d %0d %0d\", P, Q, $bits(x));\n"
                       "    $display(\"%0d\", f(1));\n"
                       "    $display(\"%0d\", f(1));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1 1\n1\n2\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim, AConstantCallSetsAnInitializedLocalAtEachCallsStart) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  function int fi(int k); static int c = 5; c = c + k;\n"
                 "    return c;\n"
                 "  endfunction\n"
                 "  function automatic int fa(int k); int c = 5; c = c + k;\n"
                 "    return c;\n"
                 "  endfunction\n"
                 "  localparam int PI = fi(1);\n"
                 "  localparam int QI = fi(1);\n"
                 "  localparam int PA = fa(1);\n"
                 "  localparam int QA = fa(1);\n"
                 "  logic [QI-1:0] xi;\n"
                 "  logic [QA-1:0] xa;\n"
                 "  initial begin\n"
                 "    $display(\"%0d %0d %0d %0d\", PI, QI, PA, QA);\n"
                 "    $display(\"%0d %0d\", $bits(xi), $bits(xa));\n"
                 "    $display(\"%0d\", fi(1));\n"
                 "    $display(\"%0d\", fi(1));\n"
                 "    $display(\"%0d\", fa(1));\n"
                 "    $display(\"%0d\", fa(1));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "6 6 6 6\n6 6\n6\n7\n6\n6\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim,
     AConstantCallOfAPackageFunctionLeavesItsLocalAtItsDefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  function int pf(int k); int c; c = c + k; return c;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module m;\n"
                       "  localparam int P = pk::pf(1);\n"
                       "  localparam int Q = pk::pf(1);\n"
                       "  initial begin\n"
                       "    $display(\"%0d %0d\", P, Q);\n"
                       "    $display(\"%0d\", pk::pf(1));\n"
                       "    $display(\"%0d\", pk::pf(1));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1\n1\n2\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim, DISABLED_AConstantFunctionCallSizesAPort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module a (input [f(3)-1:0] p);\n"
                       "  function automatic int f(int n); return n * 2; "
                       "endfunction\n"
                       "endmodule\n"
                       "module b (p, r);\n"
                       "  input [f(2)-1:0] p;\n"
                       "  localparam int L = f(5);\n"
                       "  input [L-1:0] r;\n"
                       "  function automatic int f(int n); return n * 2; "
                       "endfunction\n"
                       "endmodule\n"
                       "module m;\n"
                       "  logic [31:0] s;\n"
                       "  a ua(s);\n"
                       "  b ub(s, s);\n"
                       "  initial $display(\"%0d %0d %0d\",\n"
                       "      $bits(ua.p), $bits(ub.p), $bits(ub.r));\n"
                       "endmodule\n",
                       f),
            "6 4 10\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim, DISABLED_TheRamModelExampleSizesItsInstance) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module ram_model (address, write, chip_select, data);\n"
                 "  parameter data_width = 8;\n"
                 "  parameter ram_depth = 256;\n"
                 "  localparam addr_width = clogb2(ram_depth);\n"
                 "  input [addr_width - 1:0] address;\n"
                 "  input write, chip_select;\n"
                 "  inout [data_width - 1:0] data;\n"
                 "  function integer clogb2 (input [31:0] value);\n"
                 "    value = value - 1;\n"
                 "    for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)\n"
                 "      value = value >> 1;\n"
                 "  endfunction\n"
                 "  logic [data_width - 1:0] data_store[0:ram_depth - 1];\n"
                 "endmodule: ram_model\n"
                 "module m;\n"
                 "  logic [8:0] a_addr;\n"
                 "  logic a_wr, a_cs;\n"
                 "  wire [31:0] a_data;\n"
                 "  ram_model #(32,421) ram_a0(a_addr,a_wr,a_cs,a_data);\n"
                 "  initial $display(\"%0d %0d %0d %0d\", ram_a0.addr_width,\n"
                 "      $bits(ram_a0.address), $size(ram_a0.data_store),\n"
                 "      $bits(ram_a0.data_store[0]));\n"
                 "endmodule\n",
                 f),
      "9 9 421 32\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionSim,
     DISABLED_ATypeParameterOverrideReachesAConstantFunctionsLocal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module c #(parameter type T = logic [4:0]);\n"
                       "  function automatic int tv(); T v; v = '1; return v;\n"
                       "  endfunction\n"
                       "  localparam int TV = tv();\n"
                       "endmodule\n"
                       "module m;\n"
                       "  c #(.T(logic [6:0])) u();\n"
                       "  initial $display(\"%0d\", u.TV);\n"
                       "endmodule\n",
                       f),
            "127\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
