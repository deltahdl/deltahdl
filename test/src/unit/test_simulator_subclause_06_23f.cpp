#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.23 with §6.20.3: a comparison of two type references is true exactly
// when the two types match in the scope the comparison is written in, and each
// instance of a module, binding its own parameters, is a scope of its own, as
// is each instance of a loop generate block (§27.4). So one comparison written
// once in a module answers each instance with that instance's types.

// The comparison of `operand`'s type with `type`, under ==, !=, === and !==,
// most significant first: 4'b1010 where they match and 4'b0101 where not.
std::string Comparisons(std::string_view operand, std::string_view type) {
  return std::format(
      "{{type({0}) == type({1}), type({0}) != type({1}), "
      "type({0}) === type({1}), type({0}) !== type({1})}}",
      operand, type);
}

// A module whose parameter sets the type of x, comparing x's type with
// `type` in a procedure, a function, a continuous assignment and a variable's
// initializer, and gathering the four results in r.
std::string ComparingModule(std::string_view header, std::string_view decl,
                            std::string_view type) {
  const std::string kCompare = Comparisons("x", type);
  return std::format(
      "module {0};\n"
      "  {1}\n"
      "  bit [3:0] c, vi = {2};\n"
      "  bit [15:0] r;\n"
      "  function bit [3:0] fn(); return {2}; endfunction\n"
      "  assign c = {2};\n"
      "  initial #1 r = {{{2}, fn(), c, vi}};\n"
      "endmodule\n",
      header, decl, kCompare);
}

constexpr uint64_t kAllMatch = 0xAAAA;
constexpr uint64_t kNoneMatch = 0x5555;

TEST(TypeRefCompareInstanceSim, EachInstanceComparesItsOwnTypeParameter) {
  const std::string kModule =
      ComparingModule("m #(type T = int)", "T x;", "int");
  for (const std::string_view kTop :
       {"module t; m #(byte) b(); m #(int) a(); endmodule\n",
        "module t; m #(int) a(); m #(byte) b(); endmodule\n"}) {
    const std::string kSrc = kModule + std::string(kTop);
    SCOPED_TRACE(kTop);
    EXPECT_EQ(RunAndGet(kSrc, "a.r"), kAllMatch);
    EXPECT_EQ(RunAndGet(kSrc, "b.r"), kNoneMatch);
  }
}

TEST(TypeRefCompareInstanceSim, EachInstanceComparesItsOwnWidth) {
  const std::string kModule =
      ComparingModule("w #(int W = 8)", "logic [W-1:0] x;", "logic [7:0]");
  for (const std::string_view kTop :
       {"module t; w #(4) d(); w #(8) c(); endmodule\n",
        "module t; w #(8) c(); w #(4) d(); endmodule\n"}) {
    const std::string kSrc = kModule + std::string(kTop);
    SCOPED_TRACE(kTop);
    EXPECT_EQ(RunAndGet(kSrc, "c.r"), kAllMatch);
    EXPECT_EQ(RunAndGet(kSrc, "d.r"), kNoneMatch);
  }
}

// §25.3 and §24.3: an interface and a program are instantiated with their own
// parameters as a module is, and a task's body is judged like a function's.
TEST(TypeRefCompareInstanceSim, InterfaceProgramAndTaskCompareTheirOwnTypes) {
  const std::string kCompare = Comparisons("x", "int");
  const std::string kSrc = std::format(
      "interface ifc #(type T = int);\n"
      "  T x;\n"
      "  bit [3:0] r;\n"
      "  initial #1 r = {0};\n"
      "endinterface\n"
      "program pg #(type T = int);\n"
      "  T x;\n"
      "  bit [3:0] r;\n"
      "  initial #1 r = {0};\n"
      "endprogram\n"
      "module m #(type T = int);\n"
      "  T x;\n"
      "  bit [3:0] r;\n"
      "  task automatic tk(); r = {0}; endtask\n"
      "  initial #1 tk();\n"
      "endmodule\n"
      "module t;\n"
      "  ifc #(byte) i1(); ifc #(int) i2();\n"
      "  pg #(byte) p1(); pg #(int) p2();\n"
      "  m #(byte) m1(); m #(int) m2();\n"
      "endmodule\n",
      kCompare);
  for (const char* inst : {"i", "p", "m"}) {
    SCOPED_TRACE(inst);
    EXPECT_EQ(RunAndGet(kSrc, std::format("{}1.r", inst).c_str()), 0b0101u);
    EXPECT_EQ(RunAndGet(kSrc, std::format("{}2.r", inst).c_str()), 0b1010u);
  }
}

// §6.23 with §6.22.1(f): a bound a parameter gives is folded with the value the
// instance binds, in a localparam's value and a generate condition alike, so
// `logic [W-1:0]` matches `logic [7:0]` only where W is 8.
TEST(TypeRefCompareInstanceSim, ParameterWidthIsFoldedInConstantComparisons) {
  const std::string kSrc =
      "module w #(int W = 8);\n"
      "  localparam int K = W / 2;\n"
      "  localparam bit P = type(logic [W-1:0]) == type(logic [7:0]);\n"
      "  localparam bit Q = type(logic [K-1:0]) == type(logic [3:0]);\n"
      "  bit [2:0] r;\n"
      "  if (type(logic [W-1:0]) != type(logic [7:0])) begin : g\n"
      "    initial r[2] = 1;\n"
      "  end\n"
      "  initial r[1:0] = {P, Q};\n"
      "endmodule\n"
      "module t; w #(8) c(); w #(4) d(); endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "c.r"), 0b011u);
  EXPECT_EQ(RunAndGet(kSrc, "d.r"), 0b100u);
}

// §27.4: each iteration of a loop generate block declares v with the width
// its genvar gives, and compares the type of its own v.
TEST(TypeRefCompareInstanceSim, EachLoopIterationComparesItsOwnWidth) {
  const std::string kCompare = Comparisons("v", "logic [0:0]");
  const std::string kSrc = std::format(
      "module t;\n"
      "  bit [31:0] r;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    logic [i:0] v;\n"
      "    bit [3:0] c, vi = {0};\n"
      "    function bit [3:0] fn(); return {0}; endfunction\n"
      "    assign c = {0};\n"
      "    initial #1 r[i*16 +: 16] = {{{0}, fn(), c, vi}};\n"
      "  end\n"
      "endmodule\n",
      kCompare);
  EXPECT_EQ(RunAndGet(kSrc, "r"), (kNoneMatch << 16) | kAllMatch);
}

}  // namespace
