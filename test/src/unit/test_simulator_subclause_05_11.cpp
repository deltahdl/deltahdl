#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  const uint64_t kExpected[6] = {4, 5, 4, 5, 4, 5};
  for (int row = 1; row <= 2; ++row) {
    for (int col = 1; col <= 6; ++col) {
      auto name = "n[" + std::to_string(row) + "][" + std::to_string(col) + "]";
      auto* e = f.ctx.FindVariable(name);
      ASSERT_NE(e, nullptr) << name;
      EXPECT_EQ(e->value.ToUint64(), kExpected[col - 1]) << name;
    }
  }
}

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
