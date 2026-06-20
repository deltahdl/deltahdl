

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatElaboration, EmptyConcatElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ScalarItemsElaborate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(UnpackedArrayConcatElaboration, ArrayItemExpansion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [0:1] = '{10, 20};\n"
      "  int B [0:1] = '{30, 40};\n"
      "  int C [0:3];\n"
      "  initial begin\n"
      "    C = {A, B};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c0 = f.ctx.FindVariable("C[0]");
  auto* c1 = f.ctx.FindVariable("C[1]");
  auto* c2 = f.ctx.FindVariable("C[2]");
  auto* c3 = f.ctx.FindVariable("C[3]");
  ASSERT_NE(c0, nullptr);
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(c2, nullptr);
  ASSERT_NE(c3, nullptr);
  EXPECT_EQ(c0->value.ToUint64(), 10u);
  EXPECT_EQ(c1->value.ToUint64(), 20u);
  EXPECT_EQ(c2->value.ToUint64(), 30u);
  EXPECT_EQ(c3->value.ToUint64(), 40u);
}

TEST(UnpackedArrayConcatElaboration, AssociativeArrayTargetError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, QueueTargetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, DynamicArrayTargetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d[];\n"
      "  initial d = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// "An unpacked array concatenation may appear as the source expression in an
// assignment-like context and shall not appear in any other context." A
// fixed-size unpacked target is one of the three legal slowest-varying
// dimensions (fixed-size, queue, dynamic). Mixing array and scalar items in
// the source — the LRM's `{A, 4, 5, A, 6}` shape — must elaborate cleanly.
TEST(UnpackedArrayConcatElaboration, MixedItemsForFixedSizeTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[1:3] = '{1, 2, 3};\n"
      "  int B[1:9];\n"
      "  initial B = {A, 4, 5, A, 6};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Items in an unpacked array concatenation must have a self-determined type.
// A bare brace expression nested inside the outer concatenation has no
// self-determined type when its width does not match the target element
// width (and so cannot represent a single element), so the elaborator shall
// reject the assignment.
TEST(UnpackedArrayConcatElaboration, NestedBraceItemRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A3[1:3];\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, {32'd4, 32'd5, 32'd6, 32'd7, 32'd8, 32'd9}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// The literal `null` is only a legal item when the target's element type is
// event, class, interface class, chandle, or virtual interface. An int array
// target does not qualify, so a null item is rejected.
TEST(UnpackedArrayConcatElaboration, NullItemRejectedForIntElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, null, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// A chandle array's element type is explicitly listed by the rule as allowing
// null items, so an unpacked concatenation containing null shall elaborate
// without errors.
TEST(UnpackedArrayConcatElaboration, NullItemAllowedForChandleElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle q[$];\n"
      "  initial q = {null, null};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
