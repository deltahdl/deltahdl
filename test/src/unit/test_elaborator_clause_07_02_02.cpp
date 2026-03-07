#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, PackedStructMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { bit [3:0] lo = 5; bit [3:0] hi; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, UnpackedStructMemberDefault_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { int a = 1; int b = 2; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2.2: Members of unpacked structs containing a union shall not have
// individual default member values.
TEST(Elaboration, UnpackedStructWithUnionMemberDefault_Rejected) {
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

TEST(Elaboration, UnpackedStructWithUnionNoDefault_Allowed) {
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

// §7.2.2: Explicit init on variable overrides typedef defaults.
TEST(Elaboration, ExplicitInitOverridesDefault) {
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

}  // namespace
