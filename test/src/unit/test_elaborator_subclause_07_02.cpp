#include <gtest/gtest.h>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(StructDeclarationValidation, VoidMemberInUnpackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { void v; int a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

TEST(StructDeclarationValidation, VoidMemberInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { void v; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

TEST(StructDeclarationValidation, RandInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { rand logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random qualifier is only allowed in unpacked "
                            "structures",
                            2, "7.2"));
}

TEST(StructDeclarationValidation, RandcInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { randc bit [3:0] x; bit [3:0] y; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random qualifier is only allowed in unpacked "
                            "structures",
                            2, "7.2"));
}

TEST(StructDeclarationValidation, RandInUnpackedStruct_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { rand int a; int b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandcInUnpackedStruct_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { randc bit [7:0] x; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, UnpackedStructAcceptsAnyDataType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct {\n"
      "    real r;\n"
      "    string s;\n"
      "    logic [31:0] v;\n"
      "    byte arr [4];\n"
      "    int i;\n"
      "  } mixed;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, UnpackedStructEnumMemberAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum logic [1:0] { A, B, C } abc_e;\n"
      "  struct { abc_e sel; int payload; } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, UnpackedStructNestedStructMemberAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct {\n"
      "    struct { int x; int y; } point;\n"
      "    int id;\n"
      "  } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, VoidMemberInTaggedUnion_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union tagged { void v; int a; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, SoftUnionWithPackedDim_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft { logic [7:0] a; logic [7:0] b; } [3:0] u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, BareStructWithRealMemberClassifiedUnpacked) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct { real voltage; int count; } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, PackedDimOnStructWithoutPackedRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { logic [7:0] a; logic [7:0] b; } [3:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension on struct requires the packed "
                            "keyword",
                            2, "7.2"));
}

TEST(StructDeclarationValidation, PackedDimOnPackedStructAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } [3:0] s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, PackedDimOnPlainUnionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { logic [7:0] a; logic [7:0] b; } [3:0] u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension on union requires the packed "
                            "keyword",
                            2, "7.2"));
}

TEST(StructDeclarationValidation, VoidMemberInPlainUnionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { void v; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

TEST(StructDeclarationValidation, RealMemberIsSixtyFourBitsWide) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; real b; } ab;\n"
      "  ab s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* s = FindVar(design, "t", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->width, 96u);
}

TEST(StructDeclarationValidation,
     ShortrealAndRealtimeMembersAreFloatAndDouble) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { shortreal s; realtime t; } st;\n"
      "  st v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* v = FindVar(design, "t", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 96u);
}

TEST(StructDeclarationValidation,
     NoLayoutForAnEndlessChainOrAMemberlessStruct) {
  Arena arena;
  DataType to_b;
  to_b.kind = DataTypeKind::kNamed;
  to_b.type_name = "b_t";
  DataType to_a;
  to_a.kind = DataTypeKind::kNamed;
  to_a.type_name = "a_t";
  const TypedefMap kCycle{{"a_t", to_b}, {"b_t", to_a}};
  EXPECT_EQ(ResolvedAggregateType(to_a, kCycle, {}, arena), nullptr);

  DataType memberless;
  memberless.kind = DataTypeKind::kStruct;
  EXPECT_EQ(ResolvedAggregateType(memberless, kCycle, {}, arena), nullptr);
}

TEST(StructDeclarationValidation, AggregatesNestedInPlaceAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { union { chandle c; int i; } u; } a;\n"
      "  struct { union { void v; int i; } u; } d;\n"
      "  struct { struct packed { rand bit x; } p; } r;\n"
      "  struct { union tagged { void v; int i; } u; } ok;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "chandle type can only be used in tagged unions", 2, "7.3.2"));
  EXPECT_TRUE(ReportedError(
      diags, "void member is only allowed in tagged unions", 3, "7.2"));
  EXPECT_TRUE(ReportedError(
      diags, "random qualifier is only allowed in unpacked structures", 4,
      "7.2"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 5u) << d.message;
}

TEST(StructDeclarationValidation, AggregatesWrittenInsideTheModuleAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module top(input struct packed { real r; } p);\n"
      "  class C; union { chandle h; int i; } u; endclass\n"
      "  function struct packed { int a = 1; } f(); endfunction\n"
      "  initial begin\n"
      "    struct { union { void v; int i; } u; } s;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, "type of member 'r' is not allowed", 1, "7.2.1"));
  EXPECT_TRUE(ReportedError(
      diags, "chandle type can only be used in tagged unions", 2, "7.3.2"));
  EXPECT_TRUE(ReportedError(
      diags, "a member of a packed structure cannot carry a default value", 3,
      "7.2.2"));
  EXPECT_TRUE(ReportedError(
      diags, "void member is only allowed in tagged unions", 5, "7.2"));
}

TEST(StructDeclarationValidation, AggregatesInPackagesAndTheUnitAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef struct packed { real r; } bad_t;\n"
      "  union { chandle h; int i; } pu;\n"
      "  typedef struct { int a = 1; } dflt_t;\n"
      "endpackage\n"
      "struct { union { void v; int i; } u; } cu_var;\n"
      "module top; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, "type of member 'r' is not allowed", 2, "7.2.1"));
  EXPECT_TRUE(ReportedError(
      diags, "chandle type can only be used in tagged unions", 3, "7.3.2"));
  EXPECT_TRUE(ReportedError(
      diags, "void member is only allowed in tagged unions", 6, "7.2"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 4u) << d.message;
}

}  // namespace
