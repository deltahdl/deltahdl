#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RandomVariableTypes, RealRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc real r;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real variable 'r' can be rand but not randc", 2,
                            "18.4"));
}

TEST(RandomVariableTypes, ShortrealRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc shortreal r;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real variable 'r' can be rand but not randc", 2,
                            "18.4"));
}

TEST(RandomVariableTypes, RealRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real r;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, IntegralRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  randc bit [3:0] y;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, ObjectHandleRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class D;\n"
             "endclass\n"
             "class C;\n"
             "  randc D h;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "object handle 'h' can be rand but not randc", 4,
                            "18.4"));
}

TEST(RandomVariableTypes, ObjectHandleRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class D;\n"
             "endclass\n"
             "class C;\n"
             "  rand D h;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, UnpackedUnionRandRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef union { byte a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  rand u_t u;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked union 'u' takes neither the rand nor the randc qualifier", 3,
      "18.4"));
}

TEST(RandomVariableTypes, PackedUntaggedUnionRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef union packed { bit [7:0] a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  rand u_t u;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, PackedUntaggedUnionRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef union packed { bit [7:0] a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  randc u_t u;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, PackedTaggedUnionRandRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef union tagged packed { bit [7:0] a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  rand u_t u;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed tagged union 'u' takes neither the rand nor the randc qualifier",
      3, "18.4"));
}

TEST(RandomVariableTypes, UnpackedStructRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef struct { rand int a; int b; } s_t;\n"
             "class C;\n"
             "  rand s_t s;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, UnpackedStructRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef struct { rand int a; int b; } s_t;\n"
             "class C;\n"
             "  randc s_t s;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked structure 's' can be rand but not randc",
                            3, "18.4"));
}

TEST(RandomVariableTypes, PackedStructRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef struct packed { bit [7:0] a; bit [7:0] b; } s_t;\n"
             "class C;\n"
             "  randc s_t s;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, UnpackedStructMemberRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef struct { rand int a; int b; } s_t;\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, PackedStructMemberRandRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef struct packed { rand bit [7:0] a; bit [7:0] b; } s_t;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "random qualifier is only allowed in unpacked structures", 1, "7.2"));
}

TEST(RandomVariableTypes, PackedUnionMemberRandRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef union packed { rand bit [7:0] a; bit [7:0] b; } u_t;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "random qualifier is only allowed in unpacked structures", 1, "7.2"));
}

TEST(RandomVariableTypes, PackedStructMemberRandRejectedInsideModule) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  typedef struct packed { rand bit [7:0] a; bit [7:0] b; } s_t;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "random qualifier is only allowed in unpacked structures", 2, "7.2"));
}

TEST(RandomVariableTypes, RealtimeRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc realtime r;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real variable 'r' can be rand but not randc", 2,
                            "18.4"));
}

TEST(RandomVariableTypes, IntegralVectorRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [7:0] v;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, FourStateLogicVectorRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand logic [3:0] v;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, EnumRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef enum { RED, GREEN, BLUE } e_t;\n"
             "class C;\n"
             "  rand e_t e;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, EnumRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef enum { RED, GREEN, BLUE } e_t;\n"
             "class C;\n"
             "  randc e_t e;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, UnpackedUnionRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef union { byte a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  randc u_t u;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked union 'u' takes neither the rand nor the randc qualifier", 3,
      "18.4"));
}

TEST(RandomVariableTypes, PackedTaggedUnionRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef union tagged packed { bit [7:0] a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  randc u_t u;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed tagged union 'u' takes neither the rand nor the randc qualifier",
      3, "18.4"));
}

TEST(RandomVariableTypes, PackedStructRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef struct packed { bit [3:0] a; bit [3:0] b; } s_t;\n"
             "class C;\n"
             "  rand s_t s;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, PackedUnionMemberRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef union packed { randc bit [7:0] a; bit [7:0] b; } u_t;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "random qualifier is only allowed in unpacked structures", 1, "7.2"));
}

TEST(RandomVariableTypes, InlineForbiddenTypesAreReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand union { byte a; bit [7:0] b; } u1;\n"
             "  randc union { byte a; bit [7:0] b; } u2;\n"
             "  rand union tagged packed { bit [7:0] a; bit [7:0] b; } u3;\n"
             "  randc struct { int a; } s1;\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  const auto& d = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      d, "unpacked union 'u1' takes neither the rand nor the randc qualifier",
      2, "18.4"));
  EXPECT_TRUE(ReportedError(
      d, "unpacked union 'u2' takes neither the rand nor the randc qualifier",
      3, "18.4"));
  EXPECT_TRUE(ReportedError(d,
                            "packed tagged union 'u3' takes neither the rand "
                            "nor the randc qualifier",
                            4, "18.4"));
  EXPECT_TRUE(ReportedError(
      d, "unpacked structure 's1' can be rand but not randc", 5, "18.4"));
}

TEST(RandomVariableTypes, InlineAllowedTypesAreAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand union packed { bit [7:0] a; bit [7:0] b; } u1;\n"
             "  randc union packed { bit [7:0] a; bit [7:0] b; } u2;\n"
             "  rand struct { rand int a; } s1;\n"
             "  randc struct packed { bit [3:0] a; } s2;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, ForbiddenElementTypesOfARandArrayAreReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef union { byte a; bit [7:0] b; } uu_t;\n"
             "typedef union tagged packed { bit [7:0] a; bit [7:0] b; } "
             "tu_t;\n"
             "typedef struct { rand int a; } us_t;\n"
             "class D; endclass\n"
             "class C;\n"
             "  randc real r[2];\n"
             "  rand uu_t ua[];\n"
             "  randc tu_t ta[$];\n"
             "  randc us_t sa[2];\n"
             "  randc D ha[int];\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  const auto& d = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(d, "real variable 'r' can be rand but not randc", 6,
                            "18.4"));
  EXPECT_TRUE(ReportedError(
      d, "unpacked union 'ua' takes neither the rand nor the randc qualifier",
      7, "18.4"));
  EXPECT_TRUE(ReportedError(d,
                            "packed tagged union 'ta' takes neither the rand "
                            "nor the randc qualifier",
                            8, "18.4"));
  EXPECT_TRUE(ReportedError(
      d, "unpacked structure 'sa' can be rand but not randc", 9, "18.4"));
  EXPECT_TRUE(ReportedError(d, "object handle 'ha' can be rand but not randc",
                            10, "18.4"));
}

TEST(RandomVariableTypes, AllowedElementTypesOfARandArrayAreAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef union packed { bit [7:0] a; bit [7:0] b; } pu_t;\n"
             "typedef struct packed { bit [3:0] a; } ps_t;\n"
             "typedef struct { rand int a; } us_t;\n"
             "class D; endclass\n"
             "class C;\n"
             "  rand real r[2];\n"
             "  randc pu_t ua[];\n"
             "  randc ps_t pa[$];\n"
             "  rand us_t sa[2];\n"
             "  rand D ha[int];\n"
             "  randc bit [3:0] b[4];\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
