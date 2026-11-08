#include <gtest/gtest.h>

#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'r' is not allowed in a packed "
                            "structure",
                            2, "7.2.1"));
}

TEST(PackedStructValidation, PackedStructStringMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { string s; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 's' is not allowed in a packed "
                            "structure",
                            2, "7.2.1"));
}

TEST(PackedStructValidation, PackedStructChandleMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { chandle c; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'c' is not allowed in a packed "
                            "structure",
                            2, "7.2.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'sr' is not allowed in a packed "
                            "structure",
                            2, "7.2.1"));
}

TEST(PackedStructValidation, PackedStructRealtimeMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { realtime rt; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'rt' is not allowed in a packed "
                            "structure",
                            2, "7.2.1"));
}

TEST(PackedStructValidation, PackedStructEventMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { event e; logic [7:0] a; } ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'e' is not allowed in a packed "
                            "structure",
                            2, "7.2.1"));
}

TEST(PackedStructValidation, PackedStructUnpackedArrayMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] mem [4]; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array member 'mem' is not allowed in a "
                            "packed structure",
                            2, "7.2.1"));
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

TEST(PackedStructValidation, PackedStructRealMemberNames7_2_1) {
  ElabFixture f;
  ElabOk(
      "module top;\n"
      "  struct packed { real r; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'r' is not allowed in a packed "
                            "structure",
                            2, "7.2.1"));
}

TEST(PackedStructTyping, NamedNestedAndEnumMembersDecideTheState) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  typedef bit [3:0] bnib_t;\n"
      "  typedef enum logic [1:0] { A, B } e_t;\n"
      "  struct packed { nib_t a; bit b; } named4;\n"
      "  struct packed { bnib_t a; bit b; } named2;\n"
      "  struct packed { struct packed { logic l; } in; bit b; } nested4;\n"
      "  struct packed { e_t e; bit b; } enum4;\n"
      "  union { nib_t a; int i; } union4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const auto& vars = design->top_modules[0]->variables;
  auto is_4state = [&vars](std::string_view name) {
    for (const auto& v : vars) {
      if (v.name == name) return v.is_4state;
    }
    ADD_FAILURE() << "no variable " << name;
    return false;
  };
  EXPECT_TRUE(is_4state("named4"));
  EXPECT_FALSE(is_4state("named2"));
  EXPECT_TRUE(is_4state("nested4"));
  EXPECT_TRUE(is_4state("enum4"));
  EXPECT_TRUE(is_4state("union4"));
}

TEST(PackedStructValidation, MemberTypesAreJudgedThroughNamesAndNesting) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; endclass\n"
      "  typedef real r_t;\n"
      "  typedef struct { int a; } us_t;\n"
      "  struct packed { r_t x; bit b; } a;\n"
      "  struct packed { us_t u; bit b; } b;\n"
      "  struct packed { struct { int a; } in; bit b; } c;\n"
      "  struct { struct packed { real r; } in; } d;\n"
      "  struct packed { struct packed { bit x; } p; "
      "union packed { bit [1:0] y; bit [1:0] z; } q; "
      "union soft { bit [1:0] s; bit t; } r; enum bit { A } e; } ok;\n"
      "  struct { C h; int i = 1; } cls;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, "type of member 'x' is not allowed", 5, "7.2.1"));
  EXPECT_TRUE(
      ReportedError(diags, "type of member 'u' is not allowed", 6, "7.2.1"));
  EXPECT_TRUE(
      ReportedError(diags, "type of member 'in' is not allowed", 7, "7.2.1"));
  EXPECT_TRUE(
      ReportedError(diags, "type of member 'r' is not allowed", 8, "7.2.1"));
  for (const auto& d : diags) {
    EXPECT_NE(d.loc.line, 9u) << d.message;
    EXPECT_NE(d.loc.line, 10u) << d.message;
  }
}

}  // namespace
