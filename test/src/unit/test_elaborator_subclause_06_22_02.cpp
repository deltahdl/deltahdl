#include <gtest/gtest.h>

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
  EXPECT_TRUE(
      ElementTypesEquivalent({DataTypeKind::kInt, 32, true, false, {}},
                             {DataTypeKind::kBit, 32, true, false, {}}));
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

TEST(EquivalentTypesElaboration, TypedefElementArrayAssignmentAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef bit [10:1] uint10;\n"
             "  bit [9:0] A [0:5];\n"
             "  uint10 C [6:1];\n"
             "  initial begin\n"
             "    C = A;\n"
             "    A = C;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(EquivalentTypesElaboration, TypedefElementOfAnotherWidthRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef bit [10:1] uint10;\n"
      "  bit [8:0] A [0:5];\n"
      "  uint10 C [6:1];\n"
      "  initial C = A;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array element type mismatch in assignment "
                            "('C' vs 'A')",
                            5, "7.6"));
}

}  // namespace
