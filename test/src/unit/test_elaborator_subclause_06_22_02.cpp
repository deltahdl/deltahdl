#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §6.22.2(d): unpacked fixed-size arrays are equivalent when their element
// types are equivalent and the sizes are equal -- the actual range bounds may
// differ ([0:5] vs [1:6]).
TEST(EquivalentTypesElaboration,
     UnpackedFixedSizeArrayDifferentRangesEquivalent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  bit [7:0] a [0:5];\n"
      "  bit [7:0] b [1:6];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.2(e): dynamic arrays are equivalent when they are the same kind of
// array with equivalent element types.
TEST(EquivalentTypesElaboration, DynamicArraysSameElementTypeEquivalent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int a [];\n"
      "  int b [];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.2(e): queues are equivalent when they are the same kind of array with
// equivalent element types.
TEST(EquivalentTypesElaboration, QueuesSameElementTypeEquivalent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int a [$];\n"
      "  int b [$];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.2: two unpacked structure variables are equivalent only when they are
// declared with the same named type, so a comparison of variables of two
// different structure types is illegal. The subclause on the report is what
// tells this rejection from §6.22.1's matching-type rule, which two named
// types breach independently of whether either is an aggregate. The two type
// names are in the substring because CheckAggregateCompareOp in
// src/elaborator/elaborator_validate_operations.cpp has a second report under
// the same subclause, for whole unpacked arrays of differing size, and that
// one names no type.
TEST(EquivalentTypesElaboration, NonEquivalentStructComparisonNames6_22_2) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { logic [7:0] a; } s_t;\n"
      "  typedef struct { logic [15:0] b; } t_t;\n"
      "  s_t s;\n"
      "  t_t t;\n"
      "  logic r;\n"
      "  initial r = (s == t);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "comparison of non-equivalent aggregate types 's_t' and 't_t'", 7,
      "6.22.2"));
}

}  // namespace
