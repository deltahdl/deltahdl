#include <gtest/gtest.h>

#include <string>

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

}  // namespace
