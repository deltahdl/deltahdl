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

TEST(IpcSync, DISABLED_ElementsAndEventsOfOtherScopesCompareByTheirQueues) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  event pe;\n"
                 "endpackage\n"
                 "interface ifc;\n"
                 "  event ie;\n"
                 "endinterface\n"
                 "module sub;\n"
                 "  event se;\n"
                 "endmodule\n"
                 "module m;\n"
                 "  ifc i();\n"
                 "  sub s();\n"
                 "  event arr [2];\n"
                 "  event x, y;\n"
                 "  initial begin\n"
                 "    $display(\"arr0!=null %0d  arr0!=arr1 %0d  arr0?%0d\", "
                 "arr[0] != null, arr[0] != arr[1], arr[0] ? 1 : 0);\n"
                 "    $display(\"ie!=null %0d  se!=null %0d  pe!=null %0d\", "
                 "i.ie != null, s.se != null, pk::pe != null);\n"
                 "    $display(\"ie==pe %0d  ie==se %0d  x==y %0d  ie==x "
                 "%0d\", i.ie == pk::pe, i.ie == s.se, x == y, i.ie == x);\n"
                 "    $display(\"if(ie) %0d  if(se) %0d  if(pe) %0d\", i.ie ? "
                 "1 : 0, s.se ? 1 : 0, pk::pe ? 1 : 0);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "arr0!=null 1  arr0!=arr1 1  arr0?1\n"
      "ie!=null 1  se!=null 1  pe!=null 1\n"
      "ie==pe 0  ie==se 0  x==y 0  ie==x 0\n"
      "if(ie) 1  if(se) 1  if(pe) 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
