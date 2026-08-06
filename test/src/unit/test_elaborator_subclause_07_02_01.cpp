#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PackedStructValidation, PackedStructSigned_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed signed { int a; byte b; } ok_t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructUnsigned_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed unsigned { logic [7:0] a; } ok_t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { real r; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructStringMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { string s; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructChandleMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { chandle c; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructLogicMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructBitMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { bit [7:0] a; bit [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructIntegerTypes_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { byte a; shortint b; int c; longint d; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructTimeInteger_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed unsigned { time a; integer b; logic [31:0] c; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructShortrealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { shortreal sr; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructRealtimeMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { realtime rt; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructEventMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { event e; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructUnpackedArrayMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] mem [4]; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructRegMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { reg [7:0] a; reg [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedStructValidation, PackedStructEnumMember_Allowed) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef enum logic [1:0] { A, B, C } abc_e;\n"
             "  struct packed { abc_e x; logic [5:0] data; } s;\n"
             "endmodule\n"));
}

TEST(PackedStructValidation, NestedPackedStruct_Allowed) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef struct packed {\n"
             "    struct packed { logic [7:0] x; logic [7:0] y; } coord;\n"
             "    logic [7:0] color;\n"
             "  } pixel_t;\n"
             "  pixel_t p;\n"
             "endmodule\n"));
}

// §7.2.1: a packed data type is legal as a packed-struct member. A packed union
// is a packed data type, so it is accepted alongside the integral members
// (distinct admitted form from the nested packed struct case above).
TEST(PackedStructValidation, PackedStructPackedUnionMember_Allowed) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef struct packed {\n"
             "    logic [7:0] tag;\n"
             "    union packed { logic [7:0] a; logic [7:0] b; } u;\n"
             "  } msg_t;\n"
             "  msg_t m;\n"
             "endmodule\n"));
}

TEST(PackedStructTyping, AllTwoStateMembers_StructIsTwoState) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  struct packed { bit [7:0] a; byte b; } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->variables[0].is_4state);
}

TEST(PackedStructTyping, NoGaps_TotalWidthEqualsSumOfMemberWidths) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  struct packed { bit [7:0] a; bit [15:0] b; bit [3:0] c; } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_EQ(mod->variables[0].width, 28u);
}

TEST(PackedStructTyping, AnyFourStateMember_StructIsFourState) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  struct packed { bit [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_4state);
}

}  // namespace
