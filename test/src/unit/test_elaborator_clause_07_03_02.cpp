#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.3.2: Dynamic/chandle types may be used in tagged unions.
TEST(TaggedUnionValidation, ChandleInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { chandle Handle; int Value; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.3.2: Void members allowed in tagged unions.
TEST(TaggedUnionValidation, VoidMemberInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { void Invalid; int Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.3.2: Dynamic/string types may be used in tagged unions.
TEST(TaggedUnionValidation, StringInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { string S; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.3.2: Packed tagged union with integral members accepted.
TEST(TaggedUnionValidation, PackedTaggedUnionIntegralMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { bit [7:0] A; bit [15:0] B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.3.2: Packed tagged union members need not be the same width.
TEST(TaggedUnionValidation, PackedTaggedUnionDifferentWidths_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { bit [7:0] Narrow; bit [31:0] Wide; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.3.2: Packed tagged union members must be packed types; real is rejected.
TEST(TaggedUnionValidation, PackedTaggedUnionRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { real R; bit [63:0] B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.3.2: Multiple void members in tagged union.
TEST(TaggedUnionValidation, MultipleVoidMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { void A; void B; int C; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
