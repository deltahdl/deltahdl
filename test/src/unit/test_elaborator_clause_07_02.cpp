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

TEST(StructDeclarationValidation, VoidMemberInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { void Invalid; int Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, VoidMemberInUnpackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { void v; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, VoidMemberInPackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { void v; logic [7:0] a; } u;\n"
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

TEST(StructDeclarationValidation, RandInUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { rand int a; int b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandcInUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { randc int a; int b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, PackedDimOnUnpackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { logic [7:0] a; logic [7:0] b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, PackedDimOnUnpackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { int a; int b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
