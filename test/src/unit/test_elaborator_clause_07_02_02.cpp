#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StructAssignmentValidation, PackedStructMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { bit [3:0] lo = 5; bit [3:0] hi; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, UnpackedStructMemberDefault_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { int a = 1; int b = 2; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, UnpackedStructWithUnionMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {\n"
      "    union { int a; logic [31:0] b; } u;\n"
      "    int tag = 1;\n"
      "  } bad_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, UnpackedStructWithUnionNoDefault_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {\n"
      "    union { int a; logic [31:0] b; } u;\n"
      "    int tag;\n"
      "  } ok_t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, ExplicitInitOverridesDefault) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {\n"
      "    int addr = 100;\n"
      "    int crc;\n"
      "  } packet1;\n"
      "  packet1 p1 = '{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, UnpackedStructAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  initial y = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §7.2.2: Even when ALL members of a packed struct have defaults, still rejected.
TEST(StructAssignmentValidation, PackedStructAllMembersDefaulted_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { bit [3:0] a = 1; bit [3:0] b = 2; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.2.2: Packed struct member default rejected even via typedef.
TEST(StructAssignmentValidation, PackedStructTypedefMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] cmd = 8'hFF;\n"
      "    logic [7:0] data;\n"
      "  } msg_t;\n"
      "  msg_t m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.2.2: Unpacked struct with nested union, default on the union member itself.
TEST(StructAssignmentValidation,
     UnpackedStructWithUnionMemberDefault_OnUnionMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {\n"
      "    union { int a; logic [31:0] b; } u = 0;\n"
      "    int tag;\n"
      "  } bad_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
