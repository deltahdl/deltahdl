#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StreamReorderingElaboration, LeftShiftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {<< {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, RightShiftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {>> {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, TypeSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {<< byte {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, IntegerSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = {<< 8 {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, ZeroSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< 0 {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(StreamReorderingElaboration, NegativeSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (-1) {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A slice_size given as a folded constant expression (not a bare literal) that
// reduces to zero is just as illegal; this drives the constant-evaluation
// branch of the slice-size check rather than the literal-text branch.
TEST(StreamReorderingElaboration, ComputedZeroSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (2 - 2) {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A folded constant expression that reduces to a positive value is a legal
// slice_size and must not be flagged, confirming the check rejects only
// non-positive constants and not computed expressions generally.
TEST(StreamReorderingElaboration, ComputedPositiveSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (4 - 1) {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.14.2: the zero/negative slice_size rule applies to any constant
// expression, and §11.2.1 admits a parameter as such a constant. The check
// folds the slice_size in the module's parameter scope, so a parameter that
// resolves to zero is rejected just like a literal zero. This drives the
// scope-resolving branch of the check, distinct from the literal-text branch.
TEST(StreamReorderingElaboration, ParameterZeroSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter W = 0;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (W + 0) {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The localparam form is the other §11.2.1 named-constant slice_size. A
// localparam resolving to a positive value is legal and must not be flagged,
// confirming the scope-folded check admits a named constant and rejects only
// non-positive ones.
TEST(StreamReorderingElaboration, LocalparamPositiveSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam W = 8;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (W + 0) {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
