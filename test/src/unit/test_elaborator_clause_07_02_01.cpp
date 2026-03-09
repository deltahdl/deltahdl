#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, UnpackedStructSigned_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct signed { int f1; logic f2; } bad_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, UnpackedStructUnsigned_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct unsigned { int f1; logic f2; } bad_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructSigned_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed signed { int a; byte b; } ok_t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructUnsigned_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed unsigned { logic [7:0] a; } ok_t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { real r; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructStringMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { string s; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructChandleMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { chandle c; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructLogicMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructBitMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { bit [7:0] a; bit [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructIntegerTypes_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { byte a; shortint b; int c; longint d; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructTimeInteger_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed unsigned { time a; integer b; logic [31:0] c; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, PackedStructShortrealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { shortreal sr; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
