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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.2.2/§11.2.1: a member default is a constant expression, which may be a
// parameter reference. It must be evaluated in the module's parameter scope,
// so a parameter default is accepted (contrast the `int n` variable case
// above, which is genuinely non-constant and still errors). Uses an anonymous
// inline struct, as in the sv-tests default-value case.
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

// §7.2.2/§11.2.1: a member default is a constant expression, one form of which
// is a localparam reference. Like the parameter case, it must resolve in the
// module's parameter scope, so a localparam-valued default is accepted.
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

// §7.2.2/§11.2.1: a constant function call is another form of constant
// expression admitted as a member default. With constant arguments the call is
// accepted, a distinct code path from a plain identifier (parameter/localparam)
// reference.
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

// §7.2.2 (final sentence, see §6.7.1): the initial assignment expression within
// a data type is ignored when the type is used to declare a net without a
// user-defined nettype. The member default is legal on the (unpacked) struct
// type, and using that type as a net is accepted -- the default is not applied
// as an (illegal) net declaration assignment. The same type used as a variable
// is accepted too, confirming the type itself is well-formed.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
