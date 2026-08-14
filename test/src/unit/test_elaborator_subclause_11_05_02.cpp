
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArrayAddressingElaboration, WriteAndReadArrayElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin mem[0] = 8'h00; mem[2] = 8'hAB; end\n"
      "endmodule\n",
      f, "mem[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ArrayAddressingElaboration, MultiDimArrayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:3][0:3];\n"
             "  int result;\n"
             "  initial result = mem[1][2];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, MemoryIndirectionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:7];\n"
             "  int result;\n"
             "  initial result = mem[mem[3]];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, BitSelectAfterArrayElementElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] arr [0:3];\n"
             "  logic result;\n"
             "  initial result = arr[2][5];\n"
             "endmodule\n"));
}

// §11.5.2 — a bit-select or part-select of an array element requires an address
// for every dimension first. Addressing all dimensions, then part-selecting the
// selected word, is legal.
TEST(ArrayAddressingElaboration, PartSelectAfterAllDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] twod [0:3][0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = twod[1][2][3:0];\n"
             "endmodule\n"));
}

// §11.5.2 — the positive boundary for a three-dimensional array: once all three
// dimensions are addressed the selected item is a vector, so a part-select of
// it is legal. This is the accepting twin of the rejections below.
TEST(ArrayAddressingElaboration, PartSelectAfterAllThreeDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [3:0] result;\n"
             "  initial result = threed[2][1][0][3:0];\n"
             "endmodule\n"));
}

// The cases below all leave one dimension unaddressed, so §11.5.2's rule about
// reaching into a word does not reach them. That rule is written about
// bit-selects and part-selects of array elements — "the desired word shall
// first be selected by supplying an address for each dimension" — and §7.4.5
// defines a part-select as a selection of contiguous bits of a packed array.
// A trailing range over a dimension carrying no address selects contiguous
// *elements* instead, which §7.4.5 calls a slice and permits: "Slices of an
// array can only apply to one dimension, but other dimensions can have single
// index values in an expression." What decides these cases is therefore not the
// unaddressed dimension but the direction the range is written in.

// §11.5.1 requires the first index of a range to "address a more significant
// bit than the second expression", and §11.5.2 sends an array's ranges to that
// same rule. The third dimension is declared [0:7] and counts upward, so its
// more significant element is the one with the smaller index and [0:3] names
// its first four elements in order.
TEST(ArrayAddressingElaboration, AscendingSliceOfAnAscendingDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][0:3];\n"
             "endmodule\n"));
}

// The same declaration and the same four elements, written backwards. This is
// the shape §11.5.2 marks illegal, and the direction is what makes it so.
TEST(ArrayAddressingElaboration,
     DescendingSliceOfAnAscendingDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] threed [0:3][0:3][0:7];\n"
      "  logic [31:0] result;\n"
      "  initial result = threed[2][1][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

// The twin declaration, whose third dimension is written [7:0] and counts
// downward. The range rejected just above is the one written in order here, and
// the range accepted just above is the one written backwards. Without this pair
// a check that rejected every descending range would pass both tests above,
// because every other array in this file counts upward.
TEST(ArrayAddressingElaboration, DescendingSliceOfADescendingDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] dthreed [0:3][0:3][7:0];\n"
             "  logic [31:0] result;\n"
             "  initial result = dthreed[2][1][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     AscendingSliceOfADescendingDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] dthreed [0:3][0:3][7:0];\n"
      "  logic [31:0] result;\n"
      "  initial result = dthreed[2][1][0:3];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

// §11.5.1 ties an indexed range to the declared direction whichever way that
// direction runs: on the upward-counting `logic [0:31] b_vect` it gives
// b_vect[0 +: 8] == b_vect[0:7] and b_vect[15 -: 8] == b_vect[8:15]. An indexed
// slice therefore cannot be written backwards, and both forms name four
// elements of the upward-counting [0:7] dimension legally.
TEST(ArrayAddressingElaboration, AscendingIndexedSliceOfADimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][0 +: 4];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, DescendingIndexedSliceOfADimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][3 -: 4];\n"
             "endmodule\n"));
}

// §11.5.2's own illegal example, on the declaration the clause writes it
// against: `wire threed_array[0:255][0:255][0:7]` is an array of
// 256-by-256-by-8 single-bit elements, with no packed dimension at all, and
// threed_array[14][1][3:0] is marked "// Illegal". Its third dimension counts
// upward, so the range runs backwards over the elements it slices.
TEST(ArrayAddressingElaboration,
     DescendingSliceOfAnAscendingBitDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire threed_array [0:255][0:255][0:7];\n"
      "  wire [3:0] result;\n"
      "  assign result = threed_array[14][1][3:0];\n"
      "endmodule\n",
      f);
  // The report names §11.5.1's scalar rule, not §11.5.2's slice ordering.
  // Elaborator::ElaborateNetDecl records a net with no packed dimension in
  // scalar_var_names_, and Elaborator::TrackVarArrayInfo runs only for a
  // kVarDecl, so a net array reaches neither
  // Elaborator::CheckArrayElementPartSelectNode nor
  // Elaborator::ValidatePartSelectBounds and every index written on
  // threed_array is rejected as a select of a scalar.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}

// §7.4.2: a dimension declared by a size alone is the range [0:size-1], which
// counts upward, so a slice of it is written with the lower index first. This
// is the form reported in #2856, and the pair pins that a size records a
// direction rather than leaving one unset — read as having no direction, both
// of these would come out the same way.
TEST(ArrayAddressingElaboration, AscendingSliceOfASizedDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial r = A[1][0:1];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, DescendingSliceOfASizedDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int A[2][3];\n"
      "  logic [63:0] r;\n"
      "  initial r = A[1][1:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

// The four cases below address every dimension, so the trailing range is a
// part-select of the word the addressing selected rather than a slice. §11.5.2
// sends it to §11.5.1 -- "Once selected, bit-selects and part-selects shall be
// addressed in the same manner as net and variable bit-selects and
// part-selects" -- and §11.5.1 requires the first index to address a more
// significant bit than the second. Which index that is comes from the element's
// own declared range, so the same part-select is legal against one element
// declaration and illegal against the other.
//
// Every other array in this file declares its element [7:0]. On a range ending
// at zero the index of a bit and its distance from the least significant end
// are the same number, so those tests answer alike whether the declaration is
// consulted or ignored. The pair below is what tells the two apart: `arr` and
// `darr` differ only in the direction of the element, and the verdicts swap.

TEST(ArrayAddressingElaboration,
     AscendingPartSelectOfAnAscendingElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [0:7] arr [0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = arr[2][0:3];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     DescendingPartSelectOfAnAscendingElementIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [0:7] arr [0:3];\n"
      "  logic [3:0] result;\n"
      "  initial result = arr[2][3:0];\n"
      "endmodule\n",
      f);
  // Every dimension is addressed, so §11.5.2 hands the range to §11.5.1 and the
  // report names that clause rather than this file's.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more "
                            "significant bit",
                            4, "11.5.1"));
}

TEST(ArrayAddressingElaboration,
     DescendingPartSelectOfADescendingElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] darr [0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = darr[2][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     AscendingPartSelectOfADescendingElementIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] darr [0:3];\n"
      "  logic [3:0] result;\n"
      "  initial result = darr[2][0:3];\n"
      "endmodule\n",
      f);
  // As above: the addressing is complete, so §11.5.1 is the clause reported.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more "
                            "significant bit",
                            4, "11.5.1"));
}

}  // namespace
