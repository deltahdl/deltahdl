#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.24.3: a bit-stream cast that converts a packed value into a packed
// aggregate of the same total width is legal.
TEST(BitStreamCastElaboration, IntToPackedStructOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'(16'hCAFE);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.24.3: a fixed-size unpacked array whose total width matches the
// destination integral type elaborates without error.
TEST(BitStreamCastElaboration, UnpackedArrayMatchingSizeOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial result = int'(arr);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.24.3: an associative array type shall be illegal as a destination type
// for a bit-stream cast.
TEST(BitStreamCastElaboration, AssociativeArrayDestRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  typedef byte amap_t [string];\n"
             "  byte src;\n"
             "  amap_t dst;\n"
             "  initial dst = amap_t'(src);\n"
             "endmodule\n"));
}

// §6.24.3: a wildcard-indexed associative array is also rejected as a
// destination type.
TEST(BitStreamCastElaboration, WildcardAssocDestRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  typedef byte wmap_t [*];\n"
             "  byte src;\n"
             "  wmap_t dst;\n"
             "  initial dst = wmap_t'(src);\n"
             "endmodule\n"));
}

// §6.24.3: a class-handle-keyed associative array is also rejected as a
// destination type. Exercises the user-defined-key branch of the typedef
// tracker, which is independent of the built-in-key branch.
TEST(BitStreamCastElaboration, ClassKeyedAssocDestRejected) {
  EXPECT_FALSE(
      ElabOk("class Key;\n"
             "endclass\n"
             "module m;\n"
             "  typedef byte kmap_t [Key];\n"
             "  byte src;\n"
             "  kmap_t dst;\n"
             "  initial dst = kmap_t'(src);\n"
             "endmodule\n"));
}

// §6.24.3: alongside the associative-array prohibition, a class type is also
// illegal as a bit-stream cast destination when the source is not itself a
// class handle.
TEST(BitStreamCastElaboration, ClassDestFromNonClassRejected) {
  EXPECT_FALSE(
      ElabOk("class Container;\n"
             "endclass\n"
             "module m;\n"
             "  int src;\n"
             "  Container c;\n"
             "  initial c = Container'(src);\n"
             "endmodule\n"));
}

// §6.24.3: a class handle whose class has a local member is illegal as a
// bit-stream cast source.
TEST(BitStreamCastElaboration, ClassWithLocalSourceRejected) {
  EXPECT_FALSE(
      ElabOk("class Hidden;\n"
             "  local int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Hidden h;\n"
             "  int v;\n"
             "  initial v = int'(h);\n"
             "endmodule\n"));
}

// §6.24.3: a class handle whose class has a protected member is also illegal
// as a bit-stream cast source.
TEST(BitStreamCastElaboration, ClassWithProtectedSourceRejected) {
  EXPECT_FALSE(
      ElabOk("class Hidden;\n"
             "  protected int hidden;\n"
             "endclass\n"
             "module m;\n"
             "  Hidden h;\n"
             "  int v;\n"
             "  initial v = int'(h);\n"
             "endmodule\n"));
}

// §6.24.3: when source and destination are both fixed-size types of different
// sizes and the operand is an unpacked array, a compile-time error must be
// raised.
TEST(BitStreamCastElaboration, FixedSizeMismatchUnpackedRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  byte arr [3];\n"
             "  int result;\n"
             "  initial result = int'(arr);\n"
             "endmodule\n"));
}

// §6.24.3: a bit-stream cast to a packed struct of the wrong total width when
// the operand is an unpacked array is rejected at compile time.
TEST(BitStreamCastElaboration, UnpackedToStructWrongWidthRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } "
             "pair_t;\n"
             "  byte arr [3];\n"
             "  pair_t p;\n"
             "  initial p = pair_t'(arr);\n"
             "endmodule\n"));
}

// §6.24.3: a bit-stream cast in a continuous assignment is validated the same
// way an initial-block cast is.
TEST(BitStreamCastElaboration, ContAssignFixedSizeMismatchRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  byte arr [3];\n"
             "  int result;\n"
             "  assign result = int'(arr);\n"
             "endmodule\n"));
}

// §6.24.3: the fixed-size mismatch rule also fires when the destination is an
// unpacked-array typedef and the source is a fixed-width packed literal of a
// different total width.
TEST(BitStreamCastElaboration, FixedSizeMismatchUnpackedDestRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  typedef byte arr4_t [4];\n"
             "  arr4_t a;\n"
             "  initial a = arr4_t'(16'hABCD);\n"
             "endmodule\n"));
}

// §6.24.3: when the source's packed width matches the typedef destination's
// total unpacked width, the cast elaborates without error.
TEST(BitStreamCastElaboration, FixedSizeMatchUnpackedDestOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef byte arr4_t [4];\n"
      "  arr4_t a;\n"
      "  initial a = arr4_t'(32'hDEADBEEF);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
