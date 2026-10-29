#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <system_error>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.23 with §16.9.3: a value change function in the expression a type
// reference names is one unsigned bit, so the sum with a byte is unsigned.
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

// §6.23 with §16.9.3: `$sampled` in the expression a type reference names has
// its argument's type, eight bits here.
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

// §6.23 with §20.5: `$rtoi` in the expression a type reference names is an
// integer, `$realtobits` 64 bits and `$shortrealtobits` 32 unsigned bits.
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

// §6.23 with §20.14: `$random` and the distribution functions in the
// expression a type reference names are integers, 32 bits.
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

// §6.23 with §18.13: `$urandom` and `$urandom_range` in the expression a type
// reference names are each an int unsigned, 32 unsigned 2-state bits.
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

// §6.23 with §6.24.1 and §6.12.1: a cast to a type reference standing for a
// real type, written, declared, named by a typedef or the type of a real
// expression, converts an integral value to real, so dividing it by 2 keeps
// the half.
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

// §6.23 with §20.5 and §11.4.11: `$itor` returns a real, so an operation it is
// an operand of in the expression a type reference names is real too.
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

// §6.23 with §6.24.2 and §20.17.1: `$cast` and `$system` called as functions
// in the expression a type reference names each return an int, 32 bits.
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

// §6.23 with §19.9 and §11.4.11: `$get_coverage` returns a real, so an
// operation it is an operand of in the expression a type reference names is
// real too.
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

// §6.23: the expression a type reference names is not evaluated, so a function
// called in it, in a declaration's type or a cast's, never runs, and the
// declaration takes the type the function returns: v is an int, not the one
// bit a type no rule gave would leave it.
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

// §6.23: an increment or a decrement, before or after its operand, and an
// assignment or an operator assignment in the expression a type reference
// names are not carried out, so the variable each would change keeps its
// value.
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

// §6.23 with §18.13.1: `$urandom` in the expression a type reference names is
// not called, so the draw after it is the one the reseeded sequence gives
// second, as y is, and not its third.
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

// §6.23 with §20.14: `$random` and `$dist_uniform` in the expression a type
// reference names are not called, so neither writes back the seed variable
// it is given.
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

// §6.23 with §21.3.1: `$fopen` in the expression a type reference names is not
// called, so the file it names for writing is never created.
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

// §6.23 with §7.10.2: a queue method that removes an element, called in the
// expression a type reference names, does not run, so the queue keeps its
// size.
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

// §6.23 with §6.22.1: a comparison of a type reference to a function's call
// with another type reference matches the type the function returns, a typedef
// it is declared with read through, in a procedural statement, a continuous
// assignment, a parameter's value and a generate condition, and never calls
// the function, which the constant contexts therefore do not hold to §13.4.3's
// rules for a constant function: f reads count, a module variable.
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
