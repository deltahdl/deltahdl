#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.22.2(a): "If two types match, they are equivalent."
TEST(EquivalentTypesElaboration, MatchingTypesAreEquivalent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t a;\n"
      "  byte_t b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.2(c): "Packed arrays, packed structures, packed unions, and built-in
// integral types are equivalent if they contain the same number of total
// bits, are either all 2-state or all 4-state, and are either all signed or
// all unsigned." Two integral element types satisfying those constraints are
// equivalent per the element-equivalence predicate used by §7.6.
TEST(EquivalentTypesElaboration, PackedSameBitsSameStateAreEquivalent) {
  EXPECT_TRUE(ElementTypesEquivalent(DataTypeKind::kInt, 32, true, false,
                                     DataTypeKind::kBit, 32, true, false));
}

// §6.22.2(c) NOTE: "If any bit of a packed structure or union is 4-state, the
// entire structure or union is considered 4-state." Mixed 2/4-state types
// shall not be equivalent.
TEST(EquivalentTypesElaboration, DifferentStateNotEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kBit;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

// §6.22.2(c): same width, same state, different signedness shall not be
// equivalent.
TEST(EquivalentTypesElaboration, DifferentSignednessNotEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

// §6.22.2(c): different width shall not be equivalent even when state and
// signedness match.
TEST(EquivalentTypesElaboration, DifferentWidthNotEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  b.is_signed = true;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

// §6.22.2: elaborating an assignment between equivalent packed types shall
// succeed without diagnostics, since the elaborator delegates to
// TypesEquivalent / IsAssignmentCompatible to gate the assignment.
TEST(EquivalentTypesElaboration, EquivalentPackedAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  reg   [7:0] b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.2(b): "An anonymous enum, unpacked struct, or unpacked union type is
// equivalent to itself among data objects declared within the same
// declaration statement and no other data types." Two objects of the same
// anonymous declaration shall elaborate-and-assign cleanly.
TEST(EquivalentTypesElaboration, AnonymousStructSameDeclEquivalent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct { int A; int B; } x, y;\n"
      "  initial x = y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.2(d): "Unpacked fixed-size array types are equivalent if they have
// equivalent element types and equal size; the actual range bounds may
// differ." Two unpacked arrays of the same length and equivalent elements
// shall elaborate as equivalent.
TEST(EquivalentTypesElaboration, UnpackedFixedSizeArraySameSizeEquivalent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  bit [9:0] a [0:5];\n"
      "  bit [9:0] b [0:5];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
