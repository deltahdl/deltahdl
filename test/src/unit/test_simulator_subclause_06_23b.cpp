#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <system_error>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsAValueChangeFunctionAsABit) {
  const std::string kSrc =
      "module t;\n"
      "  logic clk;\n"
      "  byte s;\n"
      "  logic [7:0] m;\n"
      "  int e;\n"
      "  initial e = type(s + $rose(m, @(posedge clk)))'(16'h00F0);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsSampledAsItsArgumentsType) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  logic [7:0] m;\n"
      "  int d;\n"
      "  initial d = type(n + $sampled(m))'(16'hABCF);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsConversionFunctionsTypes) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  real r;\n"
      "  shortreal sr;\n"
      "  int d, e;\n"
      "  longint q;\n"
      "  initial begin\n"
      "    d = type(n + $rtoi(r))'(16'hABCF);\n"
      "    q = type(n + $realtobits(r))'(40'hAB_CDEF_0123);\n"
      "    e = type(s + $shortrealtobits(sr))'(16'h00F0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
  EXPECT_EQ(RunAndGet(kSrc, "q"), 0xABCDEF0123u);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsRandomFunctionsAsIntegers) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  int seed, d, e;\n"
      "  initial begin\n"
      "    d = type(n + $random)'(16'hABCF);\n"
      "    e = type(n + $dist_uniform(seed, 0, 9))'(16'hABCF);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xABCFu);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsUrandomAsAnIntUnsigned) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d, e;\n"
      "  bit u;\n"
      "  initial begin\n"
      "    d = type(n + $urandom_range(7))'(16'hABCF);\n"
      "    e = type(s + $urandom)'(16'h00F0);\n"
      "    u = $isunknown(type(n + $urandom)'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
}

TEST(TypeOfExprCastSim, CastToARealTypeReferenceConvertsToReal) {
  const std::string kSrc =
      "module t;\n"
      "  typedef real rt;\n"
      "  int i = 5;\n"
      "  real r, a, b, c, e;\n"
      "  initial begin\n"
      "    a = type(real)'(i) / 2;\n"
      "    b = type(r)'(i) / 2;\n"
      "    c = type(r * 2.0)'(i) / 2;\n"
      "    e = type(rt)'(i) / 2;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "a"), 2.5);
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "b"), 2.5);
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "c"), 2.5);
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "e"), 2.5);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsARealFunctionAsReal) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  int i = 5;\n"
      "  real a;\n"
      "  initial a = type(n + $itor(i))'(i) / 2;\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "a"), 2.5);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsCastAndSystemAsInts) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  int a, b, d, e;\n"
      "  initial begin\n"
      "    d = type(n + $cast(a, b))'(16'hABCF);\n"
      "    e = type(n + $system(\"true\"))'(16'hABCF);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xABCFu);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsGetCoverageAsReal) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  int i = 5;\n"
      "  real a;\n"
      "  initial a = type(n + $get_coverage())'(i) / 2;\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "a"), 2.5);
}

TEST(TypeOperandUnevaluatedSim, CalledFunctionNeverRuns) {
  const std::string kSrc =
      "module t;\n"
      "  int count = 0;\n"
      "  function int f();\n"
      "    count++;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  var type(f()) v;\n"
      "  initial v = type(f())'(16'hABCF);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "count"), 0u);
  EXPECT_EQ(RunAndGet(kSrc, "v"), 0xABCFu);
}

TEST(TypeOperandUnevaluatedSim, IncrementsAndAssignmentsLeaveTheirOperands) {
  const std::string kSrc =
      "module t;\n"
      "  int i = 5, j = 5, k = 5, m = 5, x = 1, y = 1;\n"
      "  int d;\n"
      "  initial begin\n"
      "    d = type(i++)'(16'hABCF);\n"
      "    d = type(++j)'(16'hABCF);\n"
      "    d = type(k--)'(16'hABCF);\n"
      "    d = type(--m)'(16'hABCF);\n"
      "    d = type((x = 3))'(16'hABCF);\n"
      "    d = type((y += 2))'(16'hABCF);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "i"), 5u);
  EXPECT_EQ(RunAndGet(kSrc, "j"), 5u);
  EXPECT_EQ(RunAndGet(kSrc, "k"), 5u);
  EXPECT_EQ(RunAndGet(kSrc, "m"), 5u);
  EXPECT_EQ(RunAndGet(kSrc, "x"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "y"), 1u);
}

TEST(TypeOperandUnevaluatedSim, UrandomIsNotDrawn) {
  const std::string kSrc =
      "module t;\n"
      "  int unsigned x, y, a, c;\n"
      "  int d;\n"
      "  initial begin\n"
      "    x = $urandom(5);\n"
      "    y = $urandom;\n"
      "    a = $urandom(5);\n"
      "    d = type($urandom)'(16'h00F0);\n"
      "    d = type($urandom_range(7))'(16'h00F0);\n"
      "    c = $urandom;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "c"), RunAndGet(kSrc, "y"));
}

TEST(TypeOperandUnevaluatedSim, RandomFunctionsLeaveTheirSeeds) {
  const std::string kSrc =
      "module t;\n"
      "  int s = 7, u = 7;\n"
      "  int d;\n"
      "  initial begin\n"
      "    d = type($random(s))'(16'h00F0);\n"
      "    d = type($dist_uniform(u, 0, 9))'(16'h00F0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "s"), 7u);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 7u);
}

TEST(TypeOperandUnevaluatedSim, FopenOpensNoFile) {
  namespace fs = std::filesystem;
  const std::string kPath =
      (fs::temp_directory_path() / "deltahdl_type_operand_fopen").string();
  std::error_code ec;
  fs::remove(kPath, ec);
  const std::string kSrc =
      "module t;\n"
      "  int d;\n"
      "  initial d = type($fopen(\"" +
      kPath +
      "\", \"w\"))'(16'h00F0);\n"
      "endmodule\n";
  RunAndGet(kSrc, "d");
  EXPECT_FALSE(fs::exists(kPath));
  fs::remove(kPath, ec);
}

TEST(TypeOperandUnevaluatedSim, QueueMethodRemovesNoElement) {
  const std::string kSrc =
      "module t;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  int d, n;\n"
      "  initial begin\n"
      "    d = type(q.pop_front())'(16'h00F0);\n"
      "    d = type(q.pop_back())'(16'h00F0);\n"
      "    n = q.size();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "n"), 3u);
}

TEST(TypeOperandUnevaluatedSim, ComparisonTypesACallWithoutRunningIt) {
  const std::string kSrc =
      "module t;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  int count = 0;\n"
      "  function int f();\n"
      "    count++;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  function nib_t g();\n"
      "    count++;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  localparam bit P = type(f()) == type(int);\n"
      "  logic a;\n"
      "  int r = 0, p = P, gsel;\n"
      "  assign a = type(f()) == type(int);\n"
      "  if (type(f()) == type(int)) begin : g_int\n"
      "    initial gsel = 1;\n"
      "  end else begin : g_other\n"
      "    initial gsel = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    if (type(f()) == type(int)) r = r | 1;\n"
      "    if (type(f()) != type(byte)) r = r | 2;\n"
      "    if (type(f()) == type(byte)) r = r | 4;\n"
      "    if (type(f()) === type(int)) r = r | 8;\n"
      "    if (type(g()) == type(logic [3:0])) r = r | 16;\n"
      "    if (type(g()) == type(nib_t)) r = r | 32;\n"
      "    if (type(g()) == type(bit [3:0])) r = r | 64;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b0111011u);
  EXPECT_EQ(RunAndGet(kSrc, "a"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "p"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "gsel"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "count"), 0u);
}

}  // namespace
