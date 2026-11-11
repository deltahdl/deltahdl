#include <gtest/gtest.h>

#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StructAssignmentValidation, PackedStructMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { bit [3:0] lo = 5; bit [3:0] hi; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a member of a packed structure cannot carry a default value of its own",
      2, "7.2.2"));
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

TEST(StructAssignmentValidation,
     UnpackedStructWithUnionMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {\n"
      "    union { int a; logic [31:0] b; } u;\n"
      "    int tag = 1;\n"
      "  } bad_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of an unpacked structure that contains a "
                            "union cannot carry a default value of its own",
                            2, "7.2.2"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a member of a packed structure cannot carry a default value of its own",
      2, "7.2.2"));
}

TEST(StructAssignmentValidation, NonConstantMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int n;\n"
      "  typedef struct {\n"
      "    int a = n;\n"
      "    int b;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "struct member default value must be a constant "
                            "expression",
                            3, "7.2.2"));
}

TEST(StructAssignmentValidation, ParameterMemberDefault_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  parameter c = 4'h5;\n"
      "  struct {\n"
      "    bit [3:0] lo = c;\n"
      "    bit [3:0] hi;\n"
      "  } p1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, LocalparamMemberDefault_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam c = 4'h5;\n"
      "  struct {\n"
      "    bit [3:0] lo = c;\n"
      "    bit [3:0] hi;\n"
      "  } p1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, ConstantFunctionCallMemberDefault_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function int inc;\n"
      "    input int x;\n"
      "    inc = x + 1;\n"
      "  endfunction\n"
      "  struct {\n"
      "    int a = inc(2);\n"
      "    int b;\n"
      "  } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructAssignmentValidation, StructMemberDefaultIgnoredForNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct {\n"
      "    logic [7:0] a = 8'hFF;\n"
      "    logic [7:0] b;\n"
      "  } t;\n"
      "  t v;\n"
      "  wire t w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of an unpacked structure that contains a "
                            "union cannot carry a default value of its own",
                            2, "7.2.2"));
}

TEST(StructAssignmentValidation, DefaultsJudgedThroughNestingAndNames) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union { int i; bit b; } u_t;\n"
      "  struct { struct packed { int x = 1; } p; } a;\n"
      "  struct { u_t u; int n = 1; } c;\n"
      "  struct { int n = 1; } ok;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "a member of a packed structure cannot carry a "
                            "default value of its own",
                            3, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags,
                            "a member of an unpacked structure that contains "
                            "a union cannot carry a default value of its own",
                            4, "7.2.2"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 5u) << d.message;
}

TEST(StructAssignmentValidation, UnitTypedefMemberDefaultMustBeConstant) {
  ElabFixture f;
  ElaborateSrc(
      "parameter int P = 3;\n"
      "int g = 5;\n"
      "typedef struct { int a = P; int b = g; } t;\n"
      "typedef struct { int a = P; } ok_t;\n"
      "module top; t v; ok_t w; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "struct member default value must be a constant expression", 3,
      "7.2.2"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 4u) << d.message;
}

constexpr std::string_view kPacked =
    "a member of a packed structure cannot carry a default value of its own";
constexpr std::string_view kUnion =
    "a member of an unpacked structure that contains a union cannot carry a "
    "default value of its own";
constexpr std::string_view kNotConstant =
    "struct member default value must be a constant expression";

TEST(StructAssignmentValidation,
     NonConstantMemberDefaultReportedWhereverTheTypeIsDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n"
      "  int w;\n"
      "  typedef struct { int a = w; } ib_t;\n"
      "  typedef struct { int a = 3; } ig_t;\n"
      "endinterface\n"
      "program pr;\n"
      "  int z;\n"
      "  typedef struct { int a = z; } z_t;\n"
      "endprogram\n"
      "checker ck;\n"
      "  int q;\n"
      "  typedef struct { int a = q; } q_t;\n"
      "endchecker\n"
      "module t;\n"
      "  class C;\n"
      "    int k;\n"
      "    static int sk;\n"
      "    typedef struct { int a = k; } cb_t;\n"
      "    typedef struct { int a = sk; } cs_t;\n"
      "    typedef struct { int a = 3; } cg_t;\n"
      "  endclass\n"
      "  function int cf(int x); return x * 2; endfunction\n"
      "  struct { int a = $urandom; } fs;\n"
      "  struct { int a = $clog2(8); int b = cf(3); } fk;\n"
      "  for (genvar g = 0; g < 1; g++) begin : gb\n"
      "    int y;\n"
      "    typedef struct { int a = y; } y_t;\n"
      "    typedef struct { int a = g; } g_t;\n"
      "  end\n"
      "  initial begin\n"
      "    struct { int a = fk.a; } bm;\n"
      "  end\n"
      "  i ii(); pr p();\n"
      "  ck c();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 3, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 8, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 12, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 18, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 19, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 23, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 27, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 31, "7.2.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 8u);
}

TEST(
    StructAssignmentValidation,
    DISABLED_NonConstantMemberDefaultReportedForPackageVariablesFunctionsAndSubroutineTypes) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  int v;\n"
      "  typedef struct { int a = v; } pb_t;\n"
      "  typedef struct { int a = 3; } pg_t;\n"
      "endpackage\n"
      "module t;\n"
      "  int cnt;\n"
      "  function int nc(); return cnt; endfunction\n"
      "  struct { int a = nc(); } fb;\n"
      "  task tk;\n"
      "    typedef struct { int a = cnt; } m_t;\n"
      "    typedef struct { int a = 4; } ok_t;\n"
      "  endtask\n"
      "  function void fn;\n"
      "    typedef struct { int a = cnt; } m_t;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 3, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 9, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 11, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kNotConstant, 15, "7.2.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(StructAssignmentValidation,
     PackedAndUnionMemberDefaultsReportedWhereverTheTypeIsDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef struct packed { int x = 1; } pk_t;\n"
      "  typedef struct { union { int a; } u; int n = 1; } pu_t;\n"
      "endpackage\n"
      "interface i;\n"
      "  typedef struct packed { int x = 1; } k_t;\n"
      "  typedef struct { union { int a; } u; int n = 1; } u_t;\n"
      "endinterface\n"
      "program pr;\n"
      "  typedef struct packed { int x = 1; } k_t;\n"
      "endprogram\n"
      "checker ck;\n"
      "  typedef struct packed { int x = 1; } k_t;\n"
      "endchecker\n"
      "module t;\n"
      "  class C;\n"
      "    typedef struct packed { int x = 1; } ck_t;\n"
      "    typedef struct { union { int a; } u; int n = 1; } cu_t;\n"
      "  endclass\n"
      "  typedef struct { union packed { int a; bit [31:0] b; } u; int n = 1; "
      "} a_t;\n"
      "  typedef struct { union tagged { int a; void v; } u; int n = 1; } "
      "b_t;\n"
      "  typedef struct { union packed { int a; bit [31:0] b; } u; int n; } "
      "ok_t;\n"
      "  for (genvar g = 0; g < 1; g++) begin : gb\n"
      "    typedef struct packed { int x = 1; } k_t;\n"
      "  end\n"
      "  initial begin\n"
      "    struct packed { int x = 1; } bk;\n"
      "  end\n"
      "  i ii(); pr p();\n"
      "  ck c();\n"
      "endmodule\n"
      "typedef struct packed { int x = 1; } uk_t;\n"
      "typedef struct { union { int a; } u; int n = 1; } uu_t;\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, kPacked, 2, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 3, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 6, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 7, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 10, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 13, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 17, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 18, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 20, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 21, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 24, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 27, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 32, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 33, "7.2.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 14u);
}

TEST(StructAssignmentValidation,
     DISABLED_PackedAndUnionMemberDefaultsReportedInsideTasksAndFunctions) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  task tk;\n"
      "    typedef struct packed { int x = 1; } k_t;\n"
      "    typedef struct { union { int a; } u; int n = 1; } u_t;\n"
      "    typedef struct { int n = 1; } ok_t;\n"
      "  endtask\n"
      "  function void fn;\n"
      "    typedef struct packed { int x = 1; } k_t;\n"
      "    typedef struct { union { int a; } u; int n = 1; } u_t;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, kPacked, 3, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 4, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kPacked, 8, "7.2.2"));
  EXPECT_TRUE(ReportedError(diags, kUnion, 9, "7.2.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

}  // namespace
