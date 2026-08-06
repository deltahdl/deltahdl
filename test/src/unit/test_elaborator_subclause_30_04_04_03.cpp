#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EdgeSensitiveStateDependentPathElaboration,
     FullPathWithDataSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     CoexistingUniqueByEdgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = 1;\n"
      "    if (c) (negedge clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.3 criterion: the same edge-sensitive path may carry different delays
// only when every port is referenced the same way in each declaration. Here the
// destination is a part-select in one declaration and a bit-select in the
// other, which is illegal (LRM Example 4).
TEST(EdgeSensitiveStateDependentPathElaboration,
     InconsistentPortReferenceIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk => (q[3:0] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk => (q[0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Criterion 2 also distinguishes "entire port" as a reference style:
// referencing the whole port in one declaration and a select in another for the
// same path is likewise illegal (exercises the entire-port branch of the
// consistency check).
TEST(EdgeSensitiveStateDependentPathElaboration,
     EntirePortVsBitSelectIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk => (q : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk => (q[0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Criterion 2 applies to every port on the path, not just the destination.
// Here the destination is referenced consistently (whole port) but the edge
// source is a part-select in one declaration and a bit-select in the other,
// which is illegal (exercises the source-side branch of the consistency check).
TEST(EdgeSensitiveStateDependentPathElaboration,
     InconsistentSourceReferenceIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] clk, input reset, output q);\n"
      "  reg data;\n"
      "  specify\n"
      "    if (reset) (posedge clk[3:0] => (q : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk[0] => (q : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Positive control: identical reference style across declarations is accepted,
// confirming the consistency check above does not reject matching part-selects.
TEST(EdgeSensitiveStateDependentPathElaboration,
     ConsistentPartSelectReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk => (q[3:0] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk => (q[3:0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.3 criterion 1: different delays may be assigned to the same
// edge-sensitive path only when the edge, condition, or both make each
// declaration unique. Here both declarations share the same edge, the same
// condition, and identically referenced terminals, so they are not unique and
// must be rejected.
TEST(EdgeSensitiveStateDependentPathElaboration,
     DuplicateEdgeAndConditionIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output q);\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Criterion 1 input form: identity of the "same path" is decided by the exact
// terminal, so two declarations that share edge and condition but address
// different bits are distinct paths and both are accepted. Exercises the
// literal bit-select index compared unequal (0 vs 1) in the path-identity test.
TEST(EdgeSensitiveStateDependentPathElaboration,
     DistinctBitSelectPathsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output [1:0] q);\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q[0] : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q[1] : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Criterion 1 negative, literal-index input form: repeating the identical
// bit-select terminal with the same edge and condition is not unique and must
// be rejected. Exercises the literal bit-select index compared equal (0 vs 0)
// in the path-identity test -- a different code path from the whole-port
// duplicate above.
TEST(EdgeSensitiveStateDependentPathElaboration,
     DuplicateBitSelectPathIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output [1:0] q);\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q[0] : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q[0] : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Criterion 1 negative, parameter-index input form: a parameter used as the
// bit-select index takes the identifier comparison path rather than the literal
// one, so this covers a distinct code path from the literal duplicate. Two
// declarations with the same parameter index, edge, and condition are not
// unique and must be rejected.
TEST(EdgeSensitiveStateDependentPathElaboration,
     DuplicateParameterIndexPathIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output [3:0] q);\n"
      "  localparam SEL = 1;\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q[SEL] : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q[SEL] : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Criterion 2 input form: an indexed part-select ([base +: width]) is a
// part-select for reference-style purposes, so two declarations that both use
// the indexed form are referenced consistently and elaborate. Exercises the
// indexed part-select classification, which existing tests (whole port,
// bit-select, ranged part-select) do not reach.
TEST(EdgeSensitiveStateDependentPathElaboration,
     IndexedPartSelectReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk => (q[1+:2] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk => (q[1+:2] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
