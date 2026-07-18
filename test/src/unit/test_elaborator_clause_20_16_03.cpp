#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §20.16.3: "PLA input terms, output terms, and memory shall be specified in
// ascending order." The LRM's own examples declare the memory as
// `logic [1:n] mem[1:m]`, with both the width (packed) and depth (unpacked)
// ranges ascending; such a call elaborates cleanly.
TEST(PlaAscendingOrder, AscendingMemoryAndTermsAreAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: a memory whose packed (width) range descends violates the
// ascending-order requirement.
TEST(PlaAscendingOrder, DescendingMemoryWidthIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16.3: the depth (unpacked) range of the memory is equally subject to the
// rule; a descending unpacked dimension is rejected.
TEST(PlaAscendingOrder, DescendingMemoryDepthIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [3:1];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16.3: a descending input-terms vector violates the rule.
TEST(PlaAscendingOrder, DescendingInputTermsAreRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [7:1] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16.3: a descending output-terms vector violates the rule.
TEST(PlaAscendingOrder, DescendingOutputTermsAreRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [3:1] breg;\n"
      "  initial $sync$or$plane(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16.3: an equal-bound (one-bit) range is its own ascending and descending
// form; treating it as ascending keeps a scalar-width term legal. This pins the
// boundary of the left <= right test.
TEST(PlaAscendingOrder, EqualBoundRangeIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:1] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: terms given as a concatenation of scalars carry no declared range,
// so the structural check leaves them alone — the ascending-order requirement
// on the listing order is the modeler's responsibility, not a range violation.
TEST(PlaAscendingOrder, ConcatenatedScalarTermsAreNotRangeChecked) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire a1, a2, a3, a4, a5, a6, a7;\n"
      "  logic b1, b2, b3;\n"
      "  initial $async$and$array(mem, {a1,a2,a3,a4,a5,a6,a7}, {b1,b2,b3});\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: the declared range bounds are §11.2.1 constant expressions, so a
// bound may be a parameter rather than an integer literal — the LRM's own
// example declares the memory with symbolic bounds. A parameter-valued packed
// range that folds to a descending direction must be caught the same way a
// literal descending range is; folding the bound in the module parameter scope
// is a different code path from a literal.
TEST(PlaAscendingOrder, DescendingMemoryWidthViaParameterIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  logic [P:1] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16.3: the accepting path for the same parameter input form — a
// parameter-valued packed range that folds ascending elaborates cleanly.
TEST(PlaAscendingOrder, AscendingMemoryWidthViaParameterIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  logic [1:P] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: a localparam is the other §11.2.1 constant form that a range bound
// admits. A localparam-valued unpacked (depth) bound that folds descending is
// rejected just like a literal one.
TEST(PlaAscendingOrder, DescendingMemoryDepthViaLocalparamIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  localparam Q = 3;\n"
      "  logic [1:7] mem [Q:1];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16.3, scoped against §20.16's task table: the ascending-order rule
// applies only to recognized PLA tasks. A descending memory passed to a name
// that is not one of the enumerated tasks raises no ascending-order error.
TEST(PlaAscendingOrder, NonPlaTaskNameIsNotRangeChecked) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] mem [1:3];\n"
      "  wire [7:1] awire;\n"
      "  logic [3:1] breg;\n"
      "  initial $async$xor$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
