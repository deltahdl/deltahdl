#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

TEST(EquivalentTypesElaboration, PackedSameBitsSameStateAreEquivalent) {
  EXPECT_TRUE(ElementTypesEquivalent({DataTypeKind::kInt, 32, true, false},
                                     {DataTypeKind::kBit, 32, true, false}));
}

TEST(EquivalentTypesElaboration, DifferentStateNotEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kBit;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesElaboration, DifferentSignednessNotEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesElaboration, DifferentWidthNotEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  b.is_signed = true;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

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
