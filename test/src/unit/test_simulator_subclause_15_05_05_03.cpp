#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(IpcSync, DistinctEventsCompareNotEqual) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (a == b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, MergedEventsCompareEqual) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    result = (a == b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, EventNotEqualToNullReturnsTrue) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev != null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, NullEventEqualsNull) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev == null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, DistinctEventsCompareUnequal) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (a != b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, MergedEventsCompareNotUnequal) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    result = (a != b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, CaseEqualitySameSemanticsAsEqForEvents) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    result = (a === b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, CaseInequalitySameSemanticsAsNeqForEvents) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (a !== b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, CaseEqualityDistinctEventsCompareFalse) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (a === b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, CaseEqualityNullEventComparesNull) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev === null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, CaseInequalityMergedEventsCompareFalse) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    result = (a !== b) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, CaseInequalityNonNullEventComparesNull) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev !== null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, NonNullEventDoesNotEqualNull) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev == null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, NullEventNotEqualNullIsFalse) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev != null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, CaseEqualityNonNullEventDoesNotEqualNull) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev === null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, CaseInequalityNullEventComparesNullFalse) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (ev !== null) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, NullOnLeftComparesEventOnRight) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = (null == ev) ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, NonNullEventIsTruthy) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = ev ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, NullEventIsFalsy) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = ev ? 1 : 0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
