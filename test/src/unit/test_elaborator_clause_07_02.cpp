#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StructDeclarationValidation, VoidMemberInUnpackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { void v; int a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, VoidMemberInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { void v; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { rand logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandcInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { randc bit [3:0] x; bit [3:0] y; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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

}  // namespace
