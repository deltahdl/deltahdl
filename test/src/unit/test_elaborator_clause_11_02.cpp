#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §11.2: Each operand kind from the operand list is a valid expression.
// These tests verify that complex operand kinds elaborate without errors
// when used as standalone expressions (no operator).

TEST(OperandElaboration, PackedStructAsExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p, q;\n"
      "  initial q = p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperandElaboration, PackedStructMemberAsExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x;\n"
      "  initial x = p.a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperandElaboration, PackedStructBitSelectAsExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic x;\n"
      "  initial x = p[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperandElaboration, PackedUnionAsExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union packed { logic [15:0] w; logic [15:0] v; } u_t;\n"
      "  u_t a, b;\n"
      "  initial b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperandElaboration, PackedUnionMemberAsExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union packed { logic [15:0] w; logic [15:0] v; } u_t;\n"
      "  u_t u;\n"
      "  logic [15:0] x;\n"
      "  initial x = u.w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperandElaboration, PackedUnionBitSelectAsExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union packed { logic [15:0] w; logic [15:0] v; } u_t;\n"
      "  u_t u;\n"
      "  logic x;\n"
      "  initial x = u[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
