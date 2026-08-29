// §11.5.1 Vector bit-select and part-select addressing, for the half of the
// clause that says "The actual bit that is accessed by an address is, in part,
// determined by the declaration of acc". The clause makes the point with
// `logic [15:0] acc` beside `logic [2:17] acc`, two sixteen-bit vectors in
// which the same value of an index names a different bit.
//
// Every case here declares a range that does not end at zero, or a range that
// ascends, so that the declaration is doing the work. A vector declared [N:0]
// makes an index and the bit offset it reaches the same number, and code that
// computes the offset where the index was required answers such a case
// correctly; the cases in test/src/unit/test_simulator_subclause_11_05_01a.cpp,
// where the rest of this subclause's simulator cases stand, all declare their
// vectors that way and so cannot reach this rule.
//
// The declarations driven through it are the ones a design can attach a packed
// dimension to: a module body's variable, a net, an element of an unpacked
// array, a module port, and the copy of a body variable that
// Lowerer::CreateChildModuleVariables in src/simulator/lowerer_child.cpp makes
// for an instance. Two further cases cover the selects the elaborator writes
// for itself, where nothing in the source states the index: slicing the
// right-hand side of a concatenation continuous-assign lvalue per element
// (§11.4.1) and slicing an instance array's port connection per instance
// (§23.3.3.5).
//
// Each case runs a module source through RunAndFindVar in
// lib/cpp/test_fixtures/fixture_simulator.h and reads the variable the select
// wrote its answer into, so the declared range reaches the select the way a
// design reaches it rather than through a hand-set field.

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A descending range whose low bound is 1: index 1 is the least significant
// bit, so it reads the 1 of 8'b0000_0001 rather than the 0 above it.
TEST(DeclaredRangeSelect, BitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8:1] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'b0000_0001; r = d[1]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// The index below that low bound is out of bounds even though it is a valid bit
// position of a vector of this width, so it reads x rather than a stored bit.
TEST(DeclaredRangeSelect, BitSelectBelowLowBoundReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8:1] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'hFF; r = d[0]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

// The write side of the same rule, in the form §18.13.1 writes it: the
// thirty-two bits addressed as [32:1] of a [64:1] vector are its low half, so a
// full-width value written there leaves the upper half alone.
TEST(DeclaredRangeSelect, PartSelectWriteLandsAtTheLowEndOfTheRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [64:1] addr;\n"
      "  initial begin addr = 64'd0; addr[32:1] = 32'hFFFF_FFFF; end\n"
      "endmodule\n",
      f, "addr");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// An ascending range, the direction the clause's `logic [0:31] b_vect` example
// uses: its first index addresses the most significant bit, so index 0 of a
// [0:7] vector reads the top bit of 8'b1000_0000.
TEST(DeclaredRangeSelect, AscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:7] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'b1000_0000; r = d[0]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// An ascending range that also does not start at zero -- the shape of the
// clause's `logic [2:17] acc`. Indices 1 through 4 of a [1:8] vector are its
// top four bits, so 8'hA5 (1010_0101) reads back as 4'hA.
TEST(DeclaredRangeSelect, AscendingRangePartSelectTakesTheLeadingBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:8] d;\n"
      "  logic [3:0] y;\n"
      "  initial begin d = 8'hA5; y = d[1:4]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// §11.5.1 states the indexed form against both directions at once: `b_vect[0 +:
// 8]` "== b_vect[0 : 7]" for `logic [0:31] b_vect`. The width is counted along
// the declared range, so those are the vector's eight most significant bits.
TEST(DeclaredRangeSelect, IndexedPartSelectCountsAlongAnAscendingRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:31] b_vect;\n"
      "  logic [7:0] y;\n"
      "  initial begin b_vect = 32'hA5000000; y = b_vect[0 +: 8]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// An element of an unpacked array is a vector declared with the array's element
// type, so it carries that type's range: index 1 of a [1:8] element is its most
// significant bit, reached here through the element rather than through a
// variable named in the source.
TEST(DeclaredRangeSelect, ArrayElementKeepsItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:8] mem [1:2];\n"
      "  logic r;\n"
      "  initial begin mem[1] = 8'b1000_0000; r = mem[1][1]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.5.1 makes its point about `logic [15:0] acc` and `logic [2:17] acc`, but
// what it settles is that "the actual bit that is accessed by an address is, in
// part, determined by the declaration" -- and a net is declared with a packed
// dimension in exactly the same way a variable is. So the three cases below are
// the net counterparts of the variable cases above: the low bound of a
// descending range names the least significant bit, the left bound of an
// ascending range names the most significant one, and a part-select is bounded
// by the range as written rather than by [width-1:0].
TEST(DeclaredRangeSelect, NetBitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [8:1] w;\n"
      "  wire r;\n"
      "  assign w = 8'b0000_0001;\n"
      "  assign r = w[1];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, NetAscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [1:8] w;\n"
      "  wire r;\n"
      "  assign w = 8'b1000_0000;\n"
      "  assign r = w[1];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, NetPartSelectIsBoundedByTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [64:1] w;\n"
      "  wire [31:0] r;\n"
      "  assign w = 64'hFFFF_FFFF_0000_0000;\n"
      "  assign r = w[64:33];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// A select the elaborator writes for itself is resolved against the declared
// range like any other, so §11.5.1 reaches the two places that synthesize one.
// Splitting a concatenation continuous-assign lvalue slices the right-hand side
// per element (§11.4.1), and distributing an instance array's port connection
// slices the connected signal per instance (§23.3.3.5). Both used to count bits
// from the least significant end, which names the intended bit only for a
// declaration written [N:0].
TEST(DeclaredRangeSelect, ConcatLvalueSlicesTheRhsInItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [8:1] src;\n"
      "  wire [3:0] hi;\n"
      "  wire [3:0] lo;\n"
      "  assign src = 8'b1010_0101;\n"
      "  assign {hi, lo} = src;\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(DeclaredRangeSelect, ConcatLvalueSlicesAnAscendingRhsFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [1:8] src;\n"
      "  wire [3:0] hi;\n"
      "  wire [3:0] lo;\n"
      "  assign src = 8'b1010_0101;\n"
      "  assign {hi, lo} = src;\n"
      "endmodule\n",
      f, "lo");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

// `out` is declared [3:0] so that only the connection being sliced out of a
// declared range is under test: the rightmost instance takes src[1], the least
// significant bit of `src`, and drives out[0], which is the least significant
// bit of a range where an index and a bit offset already coincide.
TEST(DeclaredRangeSelect, InstanceArrayConnectionSlicesInTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input a, output y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [4:1] src;\n"
      "  wire [3:0] out;\n"
      "  assign src = 4'b0110;\n"
      "  leaf u [3:0] (.a(src), .y(out));\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x6u);
}

// A module port carries a packed dimension the same way a variable or a net
// does, so "the actual bit that is accessed by an address is, in part,
// determined by the declaration" governs a select on a port too. A port is the
// one declaration a module header holds and no body declaration repeats, so
// these three cases put the select inside the instantiated module and read the
// scalar or vector it drives back out. Each parent signal is declared [N:0] so
// that only the port's own range is doing the work.
TEST(DeclaredRangeSelect, PortBitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input [8:1] data, output y);\n"
      "  assign y = data[1];\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire r;\n"
      "  leaf u (.data(src), .y(r));\n"
      "  initial src = 8'b0000_0001;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, PortAscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input [1:8] data, output y);\n"
      "  assign y = data[1];\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire r;\n"
      "  leaf u (.data(src), .y(r));\n"
      "  initial src = 8'b1000_0000;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, PortPartSelectIsBoundedByTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input [64:1] w, output [31:0] q);\n"
      "  assign q = w[64:33];\n"
      "endmodule\n"
      "module t;\n"
      "  logic [63:0] src;\n"
      "  wire [31:0] r;\n"
      "  leaf u (.w(src), .q(r));\n"
      "  initial src = 64'hFFFF_FFFF_0000_0000;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// The one module text the two body-variable positions are driven from. Its body
// holds the vector whose declared range is under test and the scalar the select
// writes its answer into, so each run resolves x[1] against the declaration the
// path that run puts it on created.
const char kDeclaredRangeLeaf[] =
    "module leaf;\n"
    "  logic [8:1] x;\n"
    "  logic r;\n"
    "  initial begin x = 8'b0000_0001; r = x[1]; end\n"
    "endmodule\n";

// The same module text under a parent that instantiates it, which puts its body
// declarations on the child path: Lowerer::CreateChildModuleVariables in
// src/simulator/lowerer_child.cpp creates the storage for u.x and u.r, while
// Lowerer::LowerModule in src/simulator/lowerer.cpp creates it for a variable
// of the top module.
std::string DeclaredRangeLeafInstantiated() {
  return std::string(kDeclaredRangeLeaf) +
         "module t;\n"
         "  leaf u ();\n"
         "endmodule\n";
}

// §11.5.1: "The actual bit that is accessed by an address is, in part,
// determined by the declaration" -- so `logic [8:1] x` reaches the same bit
// whether its module is the top or a child instance. Every case above declares
// its vector in the source's last module, which ElaborateSrc in
// lib/cpp/test_fixtures/fixture_simulator.h elaborates as the single top, and
// the three Port cases put a declaration under an instance on a port header
// rather than in a module body, so no case above selects through a range
// declared in an instantiated module's body. The two answers are asserted equal
// to each other rather than either against a literal, so the case fails on any
// divergence between the two paths however either comes to resolve the index.
// One design cannot hold both positions of one module -- a module is not an
// instance beneath itself -- so the same module text is run twice instead, and
// the child's answer is read under the instance-prefixed name it is stored by.
TEST(DeclaredRangeSelect, TopAndChildInstanceBodyVectorsSelectAlike) {
  SimFixture top_f;
  auto* top_r = RunAndFindVar(kDeclaredRangeLeaf, top_f, "r");
  SimFixture child_f;
  auto* child_r =
      RunAndFindVar(DeclaredRangeLeafInstantiated(), child_f, "u.r");
  ASSERT_NE(top_r, nullptr);
  ASSERT_NE(child_r, nullptr);
  EXPECT_EQ(child_r->value.ToUint64(), top_r->value.ToUint64());

  // The x/z half of the answer as well, so a divergence in which one position
  // reads x and the other reads 0 is not read as agreement on the value 0.
  EXPECT_EQ(child_r->value.words[0].bval, top_r->value.words[0].bval);
}

}  // namespace
