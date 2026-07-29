#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.4.5: the size of a part-select shall be constant while the position may be
// variable. Per §11.2.1 a constant expression may be a parameter reference, so
// an indexed part-select whose width is a parameter (with a runtime variable
// position) elaborates without error. The width is produced by a real parameter
// declaration so the constant-folding path that resolves it is exercised.
TEST(ArrayIndexingElaboration, IndexedPartSelectWidthParameterAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  parameter W = 8;\n"
             "  logic [31:0] vec;\n"
             "  logic [7:0] res;\n"
             "  int base;\n"
             "  initial res = vec[base +: W];\n"
             "endmodule\n"));
}

// The same constant-size rule admits a localparam as the width. A localparam is
// a distinct declaration form from a parameter, so it is covered separately.
TEST(ArrayIndexingElaboration, IndexedPartSelectWidthLocalparamAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  localparam W = 4;\n"
             "  logic [31:0] vec;\n"
             "  logic [3:0] res;\n"
             "  int base;\n"
             "  initial res = vec[base -: W];\n"
             "endmodule\n"));
}

// Negative form of the constant-size rule: an indexed part-select whose width
// is a run-time variable (not a constant expression) is rejected at
// elaboration. Only the size must be constant; the position (base) here is
// deliberately also a variable to show it is the width, not the position, that
// is illegal.
TEST(ArrayIndexingElaboration, NonConstantPartSelectWidthRejected) {
  EXPECT_FALSE(
      ElabOk("module t;\n"
             "  logic [31:0] vec;\n"
             "  logic [7:0] res;\n"
             "  int base;\n"
             "  int n;\n"
             "  initial res = vec[base +: n];\n"
             "endmodule\n"));
}

// §7.4.5: "Slices of an array can only apply to one dimension, but other
// dimensions can have single index values in an expression." A range on the
// second dimension with a single index on the first is exactly that shape, and
// it selects elements rather than reaching into a word, so §11.5.2's rule that
// a part-select must first address every dimension does not govern it. The
// element type is `int`, so what the range indexes is unambiguously the
// unpacked dimension and not the 32-bit word.
TEST(ArrayIndexingElaboration, SliceOfOneUnpackedDimensionAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a [0:1][0:2];\n"
             "  int res [0:1];\n"
             "  initial res = a[1][0:1];\n"
             "endmodule\n"));
}

// The same rule where the element's packed part is narrower than a word: the
// range still lands on the unaddressed unpacked dimension, so it is a slice.
// Covered separately from the `int` form because the packed width is what
// distinguishes a slice from the part-select rejected below.
TEST(ArrayIndexingElaboration, SliceOfOneDimensionWithNarrowElementAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a [0:1][0:4];\n"
             "  logic [7:0] res [0:2];\n"
             "  initial res = a[1][2:4];\n"
             "endmodule\n"));
}

// §11.5.2: "To express bit-selects or part-selects of array elements, the
// desired word shall first be selected by supplying an address for each
// dimension." With every dimension addressed, the range is a part-select of the
// selected 8-bit word and is legal -- the clause's own twod_array example.
TEST(ArrayIndexingElaboration, PartSelectOfFullyAddressedElementAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] twod_array [0:255][0:255];\n"
             "  logic [3:0] res;\n"
             "  initial res = twod_array[14][1][3:0];\n"
             "endmodule\n"));
}

// §11.5.2 marks `threed_array[14][1][3:0]` illegal on
// `wire threed_array[0:255][0:255][0:7]`. That array has no packed dimension,
// so its elements are single bits and there is no word for the range to index
// into; with the third dimension unaddressed the expression is the attempted
// part-select the clause rejects. This is the one shape the diagnostic still
// covers, so it is pinned here to keep the narrowing above from deleting it.
TEST(ArrayIndexingElaboration,
     PartSelectAcrossUnaddressedBitDimensionRejected) {
  EXPECT_FALSE(
      ElabOk("module t;\n"
             "  wire threed_array [0:255][0:255][0:7];\n"
             "  wire [3:0] res;\n"
             "  assign res = threed_array[14][1][3:0];\n"
             "endmodule\n"));
}

}  // namespace
