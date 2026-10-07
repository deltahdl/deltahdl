// §11.5.1 Vector bit-select and part-select addressing, for the half of the
// clause that says the declaration of acc helps decide which bit an address
// reaches. The clause makes the point with `logic [15:0] acc` beside
// `logic [2:17] acc`, two sixteen-bit vectors in which the same value of an
// index names a different bit.
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

#include <gtest/gtest.h>

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

// A part-select wholly below a range that does not reach zero addresses no bit
// of it, and §11.5.1 has a write there affect nothing. Indices 3 to 0 are the
// low bits of a vector declared [7:0], so code reading the indices as bit
// offsets would write the low nibble of `v` instead.
TEST(DeclaredRangeSelect, PartSelectWhollyBelowTheRangeWritesNothing) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:8] v;\n"
      "  initial begin v = 8'hA5; v[3:0] = 4'hF; end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
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
// what it settles is that the declaration helps decide which bit an address
// reaches -- and a net is declared with a packed dimension in exactly the same
// way a variable is. So the three cases below are the net counterparts of the
// variable cases above: the low bound of a descending range names the least
// significant bit, the left bound of an ascending range names the most
// significant one, and a part-select is bounded by the range as written rather
// than by [width-1:0].
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

// The same slicing over a connection declared with an ascending range, whose
// least significant bit is its right-hand index: the rightmost instance takes
// src[4] and the leftmost src[1], so 4'b0011 comes out as 4'b0011. Counting
// the instances up from src[4] as a descending range would run them off the
// top of the declaration.
TEST(DeclaredRangeSelect, InstanceArrayConnectionSlicesAnAscendingRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input a, output y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [1:4] src;\n"
      "  wire [3:0] out;\n"
      "  assign src = 4'b0011;\n"
      "  leaf u [3:0] (.a(src), .y(out));\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3u);
}

// A module port carries a packed dimension the same way a variable or a net
// does, so the rule that the declaration helps decide which bit an address
// reaches governs a select on a port too. A port is the one declaration a
// module header holds and no body declaration repeats, so these three cases put
// the select inside the instantiated module and read the scalar or vector it
// drives back out. Each parent signal is declared [N:0] so that only the port's
// own range is doing the work.
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

// §11.5.1: the declaration helps decide which bit an address reaches -- so
// `logic [8:1] x` reaches the same bit whether its module is the top or a child
// instance. Every case above declares its vector in the source's last module,
// which ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates as
// the single top, and the three Port cases put a declaration under an instance
// on a port header rather than in a module body, so no case above selects
// through a range declared in an instantiated module's body. The two answers
// are asserted equal to each other rather than either against a literal, so the
// case fails on any divergence between the two paths however either comes to
// resolve the index. One design cannot hold both positions of one module -- a
// module is not an instance beneath itself -- so the same module text is run
// twice instead, and the child's answer is read under the instance-prefixed
// name it is stored by.
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

// The declarations a procedure and a subroutine body make are declarations
// too, and the clause's appeal to the declaration says nothing about where one
// stands. Neither recorded a range: a procedure's local went through
// ExecVarDeclImpl and a body's through CreateFuncLocalVar, both of which sized
// the variable and stopped, so every such vector was addressed as [width-1:0]
// whatever its declaration wrote (#3808). 6'h2D under [15:10] puts 1,0,1,1,0,1
// at indices 15 down to 10: [13:10] is 4'b1101, 13, and [15:12] is 4'b1011, 11.
// Addressed as [5:0] both selects lie outside the vector and read x; a range
// recorded the wrong way round reads the other window's bits reversed.
TEST(DeclaredRangeSelect, ProcedureLocalKeepsItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    bit [15:10] v;\n"
      "    v = 6'h2D;\n"
      "    r = v[13:10] * 100 + v[15:12];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

TEST(DeclaredRangeSelect, SubroutineLocalKeepsItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  function int windows();\n"
      "    bit [15:10] v;\n"
      "    v = 6'h2D;\n"
      "    return v[13:10] * 100 + v[15:12];\n"
      "  endfunction\n"
      "  initial r = windows();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

// §6.18 makes a variable declared with a typedef name the type the name stands
// for, range included, and such a declaration writes no dimension of its own:
// the lowerer read the range off the declaration's DataType and a name has
// none, so `value_t v` at module scope was addressed as [5:0] however the
// typedef was written. The elaborator now sets the resolved type on the
// module-scope declaration, and a procedure's local, whose declaration the
// elaborator does not rewrite, reads the range the elaborated table records
// against the name. The same 1311 as above from both.
TEST(DeclaredRangeSelect, TypedefNameCarriesItsRangeToAModuleVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [15:10] value_t;\n"
      "  value_t v;\n"
      "  int r;\n"
      "  initial begin\n"
      "    v = 6'h2D;\n"
      "    r = v[13:10] * 100 + v[15:12];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

TEST(DeclaredRangeSelect, TypedefNameCarriesItsRangeToAProcedureLocal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [15:10] value_t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    value_t v;\n"
      "    v = 6'h2D;\n"
      "    r = v[13:10] * 100 + v[15:12];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

// The same of a class property, whose declaration decides which bits an index
// names as a variable's does (§8.3): on `logic [0:31] bv = 32'h89AB_CDEF`
// through a handle, `h.bv[8:15]` and `h.bv[8 +: 8]` are the bits 8 through 15
// counted from the left, 8'hab, and `h.bv[16 -: 8]` the bits 9 through 16,
// 8'h57. Addressed as [31:0], the selects were mirrored to 8'hcd and 8'he6.
TEST(DeclaredRangeSelect, AnAscendingPropertysSelectsFollowItsDeclaration) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C; logic [0:31] bv = 32'h89AB_CDEF; endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    $display(\"%h %h %h %b\", h.bv[8:15], h.bv[8 +: 8], h.bv[16 -: 8],\n"
      "             h.bv[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ab ab 57 1\n");
}

// A select written to that property is addressed the same way, so
// `h.bv[0:7] = 8'hFF` sets its eight most significant bits. Written through a
// stand-in that carried no range, it set the low byte.
TEST(DeclaredRangeSelect, AWriteToAnAscendingPropertysSelectFollowsIt) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C; logic [0:31] bv = 0; endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.bv[0:7] = 8'hFF; h.bv[31] = 1'b1;\n"
      "    $display(\"%h\", h.bv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ff000001\n");
}

// §11.5.1 with §7.4 and §8.5: an element of an integral array property is a
// vector of the element type, so a bit-select or part-select of it writes
// those bits and leaves the rest -- named bare in a method, through a handle,
// through the class scope and in a dynamic array -- and an ascending
// element's select follows its declaration, bit 0 of a `logic [0:7]` element
// being its most significant. Reached by no writer, each write changed
// nothing.
TEST(DeclaredRangeSelect, BitsOfAnElementOfAnArrayPropertyAreWritten) {
  SimFixture f;
  auto out = RunCapture(
      "class C;\n"
      "  int ia[2];\n"
      "  logic [0:7] la[2];\n"
      "  static bit [7:0] sb[2];\n"
      "  int da[];\n"
      "  function void m(); ia[0] = 0; ia[0][1] = 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new; h.m();\n"
      "    h.ia[1] = 0; h.ia[1][3] = 1; h.ia[1][15:8] = 8'hAB;\n"
      "    h.la[0] = 8'h00; h.la[0][0] = 1;\n"
      "    C::sb[1] = 0; C::sb[1][7:4] = 4'hF;\n"
      "    h.da = new[1]; h.da[0] = 0; h.da[0][2] = 1;\n"
      "    $display(\"%0d %h %h %h %h\", h.ia[0], h.ia[1], h.la[0], C::sb[1],\n"
      "             h.da[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0000ab08 80 f0 00000004\n");
}

}  // namespace
