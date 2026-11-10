#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

std::string InModule(std::string_view items) {
  return "module t;\n" + std::string(items) + "endmodule\n";
}

TEST(EquivalentTypesElaboration,
     AnonymousAggregatesOfOneStatementAreEquivalent) {
  ElabFixture f;
  ElaborateSrc(
      InModule("  struct {int A; int B;} AB1, AB2;\n"
               "  union {int A; int B;} U1, U2;\n"
               "  bit r;\n"
               "  initial begin AB1 = AB2; U1 = U2; r = (AB1 == AB2); end\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EquivalentTypesElaboration,
     DISABLED_AnonymousAggregateOfAnotherStatementIsNotEquivalent) {
  for (std::string_view use : {"AB3 = AB1;", "U3 = U1;", "r = (AB1 == AB3);"}) {
    std::string src = InModule(
        "  struct {int A; int B;} AB1, AB2;\n"
        "  struct {int A; int B;} AB3;\n"
        "  union {int A; int B;} U1, U2;\n"
        "  union {int A; int B;} U3;\n"
        "  bit r;\n"
        "  initial " +
        std::string(use) + "\n");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "non-equivalent",
                              LineHolding(src, use), "6.22.2"));
  }
}

TEST(EquivalentTypesElaboration, ArraysOfEquivalentElementsAreEquivalent) {
  ElabFixture f;
  ElaborateSrc(InModule("  typedef bit signed [7:0] BYTE;\n"
                        "  byte a [4];\n"
                        "  BYTE b [4];\n"
                        "  bit [9:0] A [0:5];\n"
                        "  bit [1:10] B [6];\n"
                        "  typedef bit [10:1] uint10;\n"
                        "  uint10 C [6:1];\n"
                        "  bit [3:0] m [2][3];\n"
                        "  bit [3:0] n [0:1][0:2];\n"
                        "  typedef int anint [0:0];\n"
                        "  anint x;\n"
                        "  int y [1];\n"
                        "  int a1 [string];\n"
                        "  bit signed [31:0] a4 [string];\n"
                        "  int d1 [];\n"
                        "  bit signed [31:0] d2 [];\n"
                        "  int q1 [$];\n"
                        "  bit signed [31:0] q2 [$];\n"
                        "  initial begin\n"
                        "    a = b; A = B; B = C; C = A; m = n; x = y; y = x;\n"
                        "    a1 = a4; d1 = d2; q1 = q2; d1 = q1; q1 = d1;\n"
                        "  end\n"),
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EquivalentTypesElaboration,
     DISABLED_PackedStructureIsEquivalentToABuiltInTypeOfItsShape) {
  ElabFixture f;
  ElaborateSrc(
      InModule("  typedef bit signed [7:0] BYTE;\n"
               "  typedef struct packed signed {bit [3:0] a, b;} uint8;\n"
               "  typedef struct packed {bit [6:0] a; logic b;} p_t;\n"
               "  byte a [4];\n"
               "  BYTE b [4];\n"
               "  uint8 c [4];\n"
               "  p_t pa [2];\n"
               "  logic [7:0] la [2];\n"
               "  initial begin a = c; b = c; pa = la; end\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

struct NonEquivalentPair {
  std::string_view decls;
  std::string_view use;
  std::string_view report;
  std::string_view subclause;
};

constexpr std::string_view kElementMismatch =
    "array element type mismatch in assignment";
constexpr std::string_view kIndexMismatch =
    "associative array index type mismatch in assignment";
constexpr std::string_view kArrayCompare =
    "comparison of non-equivalent aggregate array types";

constexpr NonEquivalentPair kNonEquivalentPairs[] = {
    {"  byte a [4];\n  bit [7:0] c [4];\n", "a = c;", kElementMismatch, "7.6"},
    {"  byte a [4];\n  logic signed [7:0] c [4];\n", "a = c;", kElementMismatch,
     "7.6"},
    {"  typedef struct packed {bit [6:0] a; logic b;} p_t;\n"
     "  p_t pa [2];\n  byte ba [2];\n",
     "pa = ba;", kElementMismatch, "7.6"},
    {"  int d1 [];\n  integer d3 [];\n", "d1 = d3;", kElementMismatch, "7.6"},
    {"  int q1 [$];\n  shortint q3 [$];\n", "q1 = q3;", kElementMismatch,
     "7.6"},
    {"  int a1 [string];\n  int a2 [int];\n", "a1 = a2;", kIndexMismatch,
     "7.9.9"},
    {"  int a1 [int];\n  int a5 [byte];\n", "a1 = a5;", kIndexMismatch,
     "7.9.9"},
    {"  int a [string];\n  int d [*];\n", "a = d;", kIndexMismatch, "7.9.9"},
    {"  int c [int];\n  int d [*];\n", "c = d;", kIndexMismatch, "7.9.9"},
    {"  bit [3:0] m [2][3];\n  bit [3:0] o [3][2];\n", "m = o;",
     "array size mismatch", "7.6"},
    {"  int dd [];\n  int qq [$];\n  bit r;\n", "r = (dd == qq);",
     kArrayCompare, "6.22.2"},
    {"  int q1 [$];\n  shortint q3 [$];\n  bit r;\n", "r = (q1 == q3);",
     kArrayCompare, "6.22.2"},
};

TEST(EquivalentTypesElaboration, NonEquivalentElementsOrIndexesAreReported) {
  for (const auto& pair : kNonEquivalentPairs) {
    std::string src = InModule(std::string(pair.decls) + "  initial " +
                               std::string(pair.use) + "\n");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(pair.report),
                              LineHolding(src, pair.use),
                              std::string(pair.subclause)));
  }
}

TEST(EquivalentTypesElaboration, DISABLED_ArrayOfAnintIsNotAnArrayOfInt) {
  std::string src = InModule(
      "  typedef int anint [0:0];\n"
      "  anint xa [2];\n"
      "  int ya [2];\n"
      "  initial xa = ya;\n");
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(kElementMismatch),
                            LineHolding(src, "xa = ya"), "7.6"));
}

constexpr std::string_view kClauseExample =
    "package p1; typedef struct {int A;} t_1; endpackage\n"
    "typedef struct {int A;} t_2;\n"
    "module sub();\n"
    "  import p1::t_1;\n"
    "  parameter type t_3 = int;\n"
    "  parameter type t_4 = int;\n"
    "  typedef struct {int A;} t_5;\n"
    "  t_1 v1; t_2 v2; t_3 v3; t_4 v4; t_5 v5;\n"
    "endmodule\n"
    "module top();\n"
    "  typedef struct {int A;} t_6;\n"
    "  sub #(.t_3(t_6)) s1 ();\n"
    "  sub #(.t_3(t_6)) s2 ();\n"
    "  initial begin\n"
    "    s1.v1 = s2.v1;\n"
    "    s1.v2 = s2.v2;\n"
    "    s1.v3 = s2.v3;\n"
    "    s1.v4 = s2.v4;\n"
    "    s1.v5 = s2.v5;\n"
    "  end\n"
    "endmodule\n";

TEST(EquivalentTypesElaboration, ClauseExampleRejectsOnlyTheInstancesOwnTypes) {
  std::string src(kClauseExample);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'s1.v5' and 's2.v5' have types the instances",
                            LineHolding(src, "s1.v5 = s2.v5"), "6.22"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
