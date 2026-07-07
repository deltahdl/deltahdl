#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §5.11 — an array literal admits the replication operator, and a replication
// may be nested inside another. The inner brace pair is removed and each
// replication operates within a single dimension: for a [1:2][1:6] array,
// '{2{'{3{4, 5}}}} fills both rows with the alternating body 4,5,4,5,4,5.
// Driven through the full pipeline via a procedural whole-array assignment so
// the produced element values can be observed.
TEST(ArrayLiteralSim, NestedReplicationOperatesWithinOneDimension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int n [1:2][1:6];\n"
      "  initial n = '{2{'{3{4, 5}}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const uint64_t expected[6] = {4, 5, 4, 5, 4, 5};
  for (int row = 1; row <= 2; ++row) {
    for (int col = 1; col <= 6; ++col) {
      auto name = "n[" + std::to_string(row) + "][" + std::to_string(col) + "]";
      auto* e = f.ctx.FindVariable(name);
      ASSERT_NE(e, nullptr) << name;
      EXPECT_EQ(e->value.ToUint64(), expected[col - 1]) << name;
    }
  }
}

// §5.11 — the replication operator is allowed within an array literal alongside
// an ordinary nested literal; the brace nesting still follows the array's
// dimensions. For a [1:2][1:3] array, '{'{0, 1, 2}, '{3{4}}} gives the first
// row 0,1,2 and fills the second row with 4,4,4.
TEST(ArrayLiteralSim, ReplicationAllowedBesideNestedLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int n [1:2][1:3];\n"
      "  initial n = '{'{0, 1, 2}, '{3{4}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("n[1][1]")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("n[1][2]")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("n[1][3]")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("n[2][1]")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("n[2][2]")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("n[2][3]")->value.ToUint64(), 4u);
}

// §5.11 — an array literal can use an index as a key together with a default
// key value; the default fills every index the explicit keys do not cover.
// For a typedef'd [1:3] array, '{1:1, default:0} assigns index 1 the value 1
// and leaves indices 2 and 3 at 0. Uses a declaration initializer (an
// assignment-like context, §10.8) so the literal's type is implicit.
TEST(ArrayLiteralSim, IndexKeyWithDefaultFillsRemaining) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int triple [1:3];\n"
      "  triple b = '{1:1, default:0};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("b[1]")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b[2]")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b[3]")->value.ToUint64(), 0u);
}

// §5.11 — an array literal's members are constant member expressions. A member
// may be a parameter reference (and an expression over it), which resolves
// through a different evaluation path than a plain integer literal. Built from
// a real `parameter` declaration and observed end-to-end.
TEST(ArrayLiteralSim, ParameterMembersAreConstantExpressions) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 5;\n"
      "  int arr [0:2];\n"
      "  initial arr = '{P, P + 1, P + 2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 7u);
}

// §5.11 — a constant array-literal member may also be a localparam constant
// expression; observed end-to-end from a real `localparam` declaration.
TEST(ArrayLiteralSim, LocalparamMembersAreConstantExpressions) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int Q = 10;\n"
      "  int arr [0:2];\n"
      "  initial arr = '{Q, Q + 5, Q + 10};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 15u);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 20u);
}

// §5.11 — an array literal may use a data type as a key (paired with a default
// key); every element of the matching type takes the type-keyed value, so the
// type key wins over the default here. Driven via a procedural whole-array
// assignment so the produced element values can be observed.
TEST(ArrayLiteralSim, TypeKeyAssignsMatchingElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial arr = '{int: 42, default: 0};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 42u);
}

}  // namespace
