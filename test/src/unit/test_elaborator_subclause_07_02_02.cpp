#include <gtest/gtest.h>

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

}  // namespace
