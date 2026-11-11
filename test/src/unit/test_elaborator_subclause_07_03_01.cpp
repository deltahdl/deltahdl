#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kNotIntegral =
    "type of member 'a' is not allowed in a packed union";
constexpr std::string_view kUnpackedArray =
    "unpacked array member 'a' is not allowed in a packed union";
constexpr std::string_view kUnequalWidths =
    "packed union member 'b' has width 16 but first member 'a' has width 8";

TEST(PackedUnionValidation, HardPackedUnion_SameWidth_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, HardPackedUnion_DifferentWidth_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed union member 'b' has width 16 but first "
                            "member 'a' has width 8",
                            2, "7.3.1"));
}

TEST(PackedUnionValidation, PackedUnionRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { real r; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'r' is not allowed in a packed "
                            "union",
                            2, "7.2.1"));
}

TEST(PackedUnionValidation, PackedUnionStringMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { string s; logic [7:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 's' is not allowed in a packed "
                            "union",
                            2, "7.2.1"));
}

TEST(PackedUnionValidation, PackedUnionIntegralMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [31:0] word; logic [3:0][7:0] bytes; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, SoftPackedUnionIntegralMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft packed { bit [7:0] a; bit [3:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, PackedUnionChandleMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { chandle c; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'c' is not allowed in a packed "
                            "union",
                            2, "7.2.1"));
}

TEST(PackedUnionValidation, SoftWithoutPackedKeyword_ValidatedAsPacked) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, SoftUnionRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { real r; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'r' is not allowed in a packed "
                            "union",
                            2, "7.2.1"));
}

TEST(PackedUnionValidation, PackedUnionShortrealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { shortreal r; logic [31:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'r' is not allowed in a packed "
                            "union",
                            2, "7.2.1"));
}

TEST(PackedUnionValidation, SoftPackedUnionPredefinedIntegralKinds_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed { byte b; shortint s; integer i; time t; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 64u);
}

TEST(PackedUnionValidation, SoftPackedUnionTimeMemberIsSixtyFourBits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed { byte b; time t; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 64u);
}

TEST(PackedUnionValidation, MixedStateIntegerAndInt_UnionIs4State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { integer a; int b; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_4state);
}

TEST(PackedUnionValidation, NestedPackedStructInPackedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed {\n"
      "    struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "    logic [7:0] flat;\n"
      "  } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, EnumMemberInPackedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum logic [7:0] { A = 0, B = 1 } my_enum;\n"
      "  union packed { my_enum e; logic [7:0] raw; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, HardPackedThreeMembers_ThirdDiffers_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; logic [3:0] c; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed union member 'c' has width 4 but first "
                            "member 'a' has width 8",
                            2, "7.3.1"));
}

TEST(PackedUnionValidation, MixedStateMembers_UnionIs4State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; bit [7:0] b; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_4state);
}

TEST(PackedUnionValidation, AllTwoStateMembers_UnionIs2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { bit [7:0] a; bit [7:0] b; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_FALSE(vars[0].is_4state);
}

TEST(PackedUnionValidation, SoftPackedUnion_WidthIsMaxOfMembers) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed { bit [7:0] narrow; bit [23:0] wide; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 24u);
}

TEST(PackedUnionValidation,
     SoftPackedUnion_PredefinedIntegralKinds_WidthIsLongest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed { bit [3:0] tiny; int mid; longint widest; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 64u);
}

TEST(PackedUnionValidation, NestedSoftPackedUnion_WidthRecursesToOuterMax) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed {\n"
      "    bit [3:0] tiny;\n"
      "    union soft packed { bit [11:0] inner_wide; bit [5:0] inner_narrow; "
      "} "
      "nested;\n"
      "  } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 12u);
}

TEST(PackedUnionValidation,
     NonIntegralMemberReportedWhereverTheUnionIsDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "typedef union packed { real a; bit [63:0] b; } cu0_t;\n"
      "typedef union soft { shortreal a; bit [31:0] b; } cu1_t;\n"
      "typedef union packed { int a; bit [31:0] b; } cu2_t;\n"
      "typedef union soft { byte a; bit [31:0] b; } cu3_t;\n"
      "package pk;\n"
      "  typedef union packed { real a; bit [63:0] b; } pk0_t;\n"
      "  typedef union soft { shortreal a; bit [31:0] b; } pk1_t;\n"
      "  typedef union packed { int a; bit [31:0] b; } pk2_t;\n"
      "  typedef union soft { byte a; bit [31:0] b; } pk3_t;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  union packed { real a; bit [63:0] b; } i0;\n"
      "  union soft { shortreal a; bit [31:0] b; } i1;\n"
      "  union packed { int a; bit [31:0] b; } i2;\n"
      "  union soft { byte a; bit [31:0] b; } i3;\n"
      "endinterface\n"
      "program pr;\n"
      "  union packed { real a; bit [63:0] b; } p0;\n"
      "  union soft { shortreal a; bit [31:0] b; } p1;\n"
      "  union packed { int a; bit [31:0] b; } p2;\n"
      "  union soft { byte a; bit [31:0] b; } p3;\n"
      "endprogram\n"
      "checker ck;\n"
      "  union packed { real a; bit [63:0] b; } c0;\n"
      "  union soft { shortreal a; bit [31:0] b; } c1;\n"
      "  union packed { int a; bit [31:0] b; } c2;\n"
      "  union soft { byte a; bit [31:0] b; } c3;\n"
      "endchecker\n"
      "class K;\n"
      "  union packed { real a; bit [63:0] b; } k0;\n"
      "  union soft { shortreal a; bit [31:0] b; } k1;\n"
      "  union packed { int a; bit [31:0] b; } k2;\n"
      "  union soft { byte a; bit [31:0] b; } k3;\n"
      "endclass\n"
      "module top;\n"
      "  ifc ii(); pr p(); ck c();\n"
      "  if (1) begin : g\n"
      "    union packed { real a; bit [63:0] b; } g0;\n"
      "    union soft { shortreal a; bit [31:0] b; } g1;\n"
      "    union packed { int a; bit [31:0] b; } g2;\n"
      "    union soft { byte a; bit [31:0] b; } g3;\n"
      "  end\n"
      "  function automatic void f;\n"
      "    union packed { real a; bit [63:0] b; } f0;\n"
      "    union soft { shortreal a; bit [31:0] b; } f1;\n"
      "    union packed { int a; bit [31:0] b; } f2;\n"
      "    union soft { byte a; bit [31:0] b; } f3;\n"
      "  endfunction\n"
      "  task automatic t;\n"
      "    union packed { real a; bit [63:0] b; } t0;\n"
      "    union soft { shortreal a; bit [31:0] b; } t1;\n"
      "    union packed { int a; bit [31:0] b; } t2;\n"
      "    union soft { byte a; bit [31:0] b; } t3;\n"
      "  endtask\n"
      "  initial begin\n"
      "    union packed { real a; bit [63:0] b; } b0;\n"
      "    union soft { shortreal a; bit [31:0] b; } b1;\n"
      "    union packed { int a; bit [31:0] b; } b2;\n"
      "    union soft { byte a; bit [31:0] b; } b3;\n"
      "  end\n"
      "  cu0_t x0; cu1_t x1; cu2_t x2; cu3_t x3;\n"
      "  pk::pk0_t y0; pk::pk1_t y1; pk::pk2_t y2; pk::pk3_t y3;\n"
      "  union packed { real a; bit [63:0] b; } m0;\n"
      "  union soft { shortreal a; bit [31:0] b; } m1;\n"
      "  union packed { int a; bit [31:0] b; } m2;\n"
      "  union soft { byte a; bit [31:0] b; } m3;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {1,  2,  6,  7,  12, 13, 18, 19, 24, 25, 30,
                        31, 38, 39, 44, 45, 50, 51, 56, 57, 63, 64}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotIntegral, line, "7.2.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 22u);
}

TEST(PackedUnionValidation,
     UnequalHardPackedMembersReportedWhereverTheUnionIsDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "typedef union packed { bit [7:0] a; bit [15:0] b; } cu0_t;\n"
      "typedef union packed { bit [15:0] a; bit [15:0] b; } cu1_t;\n"
      "typedef union soft { bit [7:0] a; bit [15:0] b; } cu2_t;\n"
      "typedef union soft packed { bit [7:0] a; bit [15:0] b; } cu3_t;\n"
      "package pk;\n"
      "  typedef union packed { bit [7:0] a; bit [15:0] b; } pk0_t;\n"
      "  typedef union packed { bit [15:0] a; bit [15:0] b; } pk1_t;\n"
      "  typedef union soft { bit [7:0] a; bit [15:0] b; } pk2_t;\n"
      "  typedef union soft packed { bit [7:0] a; bit [15:0] b; } pk3_t;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  union packed { bit [7:0] a; bit [15:0] b; } i0;\n"
      "  union packed { bit [15:0] a; bit [15:0] b; } i1;\n"
      "  union soft { bit [7:0] a; bit [15:0] b; } i2;\n"
      "  union soft packed { bit [7:0] a; bit [15:0] b; } i3;\n"
      "endinterface\n"
      "program pr;\n"
      "  union packed { bit [7:0] a; bit [15:0] b; } p0;\n"
      "  union packed { bit [15:0] a; bit [15:0] b; } p1;\n"
      "  union soft { bit [7:0] a; bit [15:0] b; } p2;\n"
      "  union soft packed { bit [7:0] a; bit [15:0] b; } p3;\n"
      "endprogram\n"
      "checker ck;\n"
      "  union packed { bit [7:0] a; bit [15:0] b; } c0;\n"
      "  union packed { bit [15:0] a; bit [15:0] b; } c1;\n"
      "  union soft { bit [7:0] a; bit [15:0] b; } c2;\n"
      "  union soft packed { bit [7:0] a; bit [15:0] b; } c3;\n"
      "endchecker\n"
      "class K;\n"
      "  union packed { bit [7:0] a; bit [15:0] b; } k0;\n"
      "  union packed { bit [15:0] a; bit [15:0] b; } k1;\n"
      "  union soft { bit [7:0] a; bit [15:0] b; } k2;\n"
      "  union soft packed { bit [7:0] a; bit [15:0] b; } k3;\n"
      "endclass\n"
      "module top;\n"
      "  ifc ii(); pr p(); ck c();\n"
      "  if (1) begin : g\n"
      "    union packed { bit [7:0] a; bit [15:0] b; } g0;\n"
      "    union packed { bit [15:0] a; bit [15:0] b; } g1;\n"
      "    union soft { bit [7:0] a; bit [15:0] b; } g2;\n"
      "    union soft packed { bit [7:0] a; bit [15:0] b; } g3;\n"
      "  end\n"
      "  function automatic void f;\n"
      "    union packed { bit [7:0] a; bit [15:0] b; } f0;\n"
      "    union packed { bit [15:0] a; bit [15:0] b; } f1;\n"
      "    union soft { bit [7:0] a; bit [15:0] b; } f2;\n"
      "    union soft packed { bit [7:0] a; bit [15:0] b; } f3;\n"
      "  endfunction\n"
      "  task automatic t;\n"
      "    union packed { bit [7:0] a; bit [15:0] b; } t0;\n"
      "    union packed { bit [15:0] a; bit [15:0] b; } t1;\n"
      "    union soft { bit [7:0] a; bit [15:0] b; } t2;\n"
      "    union soft packed { bit [7:0] a; bit [15:0] b; } t3;\n"
      "  endtask\n"
      "  initial begin\n"
      "    union packed { bit [7:0] a; bit [15:0] b; } b0;\n"
      "    union packed { bit [15:0] a; bit [15:0] b; } b1;\n"
      "    union soft { bit [7:0] a; bit [15:0] b; } b2;\n"
      "    union soft packed { bit [7:0] a; bit [15:0] b; } b3;\n"
      "  end\n"
      "  cu0_t x0; cu1_t x1; cu2_t x2; cu3_t x3;\n"
      "  pk::pk0_t y0; pk::pk1_t y1; pk::pk2_t y2; pk::pk3_t y3;\n"
      "  union packed { bit [7:0] a; bit [15:0] b; } m0;\n"
      "  union packed { bit [15:0] a; bit [15:0] b; } m1;\n"
      "  union soft { bit [7:0] a; bit [15:0] b; } m2;\n"
      "  union soft packed { bit [7:0] a; bit [15:0] b; } m3;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {1, 6, 12, 18, 24, 30, 38, 44, 50, 56, 63}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kUnequalWidths, line, "7.3.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 11u);
}

TEST(PackedUnionValidation,
     UnpackedAggregateEventAndVirtualInterfaceMembersReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; endinterface\n"
      "typedef struct { bit [7:0] x; } us_t;\n"
      "typedef union { bit [7:0] x; } uu_t;\n"
      "module top;\n"
      "  union packed { struct { bit [7:0] x; } a; bit [7:0] b; } h2;\n"
      "  union packed { us_t a; bit [7:0] b; } h3;\n"
      "  union packed { union { bit [7:0] x; } a; bit [7:0] b; } h4;\n"
      "  union packed { uu_t a; bit [7:0] b; } h5;\n"
      "  union packed { event a; bit [63:0] b; } h6;\n"
      "  union packed { virtual ifc a; bit [63:0] b; } h7;\n"
      "  union soft { struct { bit [7:0] x; } a; bit [7:0] b; } s2;\n"
      "  union soft { us_t a; bit [7:0] b; } s3;\n"
      "  union soft { union { bit [7:0] x; } a; bit [7:0] b; } s4;\n"
      "  union soft { uu_t a; bit [7:0] b; } s5;\n"
      "  union soft { event a; bit [63:0] b; } s6;\n"
      "  union soft { virtual ifc a; bit [63:0] b; } s7;\n"
      "endmodule\n",
      f);
  for (uint32_t line = 5; line <= 16; ++line) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotIntegral, line, "7.2.1"))
        << line;
  }
}

TEST(PackedUnionValidation,
     DynamicArrayQueueAndAssociativeArrayMembersReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { bit [7:0] a [1]; bit [7:0] b; } h0;\n"
      "  union packed { bit [7:0] a []; bit [7:0] b; } h1;\n"
      "  union packed { bit [7:0] a [$]; bit [7:0] b; } h2;\n"
      "  union packed { bit [7:0] a [int]; bit [7:0] b; } h3;\n"
      "  union soft { bit [7:0] a [1]; bit [7:0] b; } s0;\n"
      "  union soft { bit [7:0] a []; bit [7:0] b; } s1;\n"
      "  union soft { bit [7:0] a [$]; bit [7:0] b; } s2;\n"
      "  union soft { bit [7:0] a [int]; bit [7:0] b; } s3;\n"
      "  union packed { bit [7:0] a; bit [7:0] b; } ok1;\n"
      "  union soft { bit [7:0] a; bit [7:0] b; } ok2;\n"
      "endmodule\n",
      f);
  for (uint32_t line = 2; line <= 9; ++line) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kUnpackedArray, line, "7.2.1"))
        << line;
  }
}

TEST(PackedUnionValidation, DISABLED_ClassHandleMembersReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "typedef C ct_t;\n"
      "module top;\n"
      "  class L; endclass\n"
      "  union packed { C a; bit [63:0] b; } h1;\n"
      "  union packed { ct_t a; bit [63:0] b; } h2;\n"
      "  union packed { L a; bit [63:0] b; } h3;\n"
      "  union soft { C a; bit [63:0] b; } s1;\n"
      "  union soft { ct_t a; bit [63:0] b; } s2;\n"
      "  union soft { L a; bit [63:0] b; } s3;\n"
      "  union packed { bit [63:0] a; bit [63:0] b; } ok1;\n"
      "endmodule\n",
      f);
  for (uint32_t line = 5; line <= 10; ++line) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotIntegral, line, "7.2.1"))
        << line;
  }
}

}  // namespace
