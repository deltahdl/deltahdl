#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(AssocLiteral, DeclLiteralStringKeysSeedsEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  integer tab[string] = '{\"Peter\":20, \"Paul\":22, \"Mary\":23, "
      "default:-1};\n"
      "  int result;\n"
      "  initial result = tab[\"Peter\"];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocLiteral, DeclLiteralIntKeysSeedsEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{3:30, 7:70};\n"
      "  int result;\n"
      "  initial result = aa[7];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 70u);
}

TEST(AssocLiteral, DeclLiteralValueFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter integer P = 22;\n"
      "  integer tab[string] = '{\"x\":P, default:-1};\n"
      "  int result;\n"
      "  initial result = tab[\"x\"];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 22u);
}

TEST(AssocLiteral, DeclLiteralValueFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int Q = 33;\n"
      "  int aa[int] = '{5:Q};\n"
      "  int result;\n"
      "  initial result = aa[5];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

TEST(AssocLiteral, RuntimeLiteralReplacesWholeContents) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocLiteral, RuntimeLiteralDropsPriorEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocLiteral, RuntimeLiteralEstablishesNewEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa[6];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

TEST(AssocLiteral, RuntimeLiteralStringKeyedReplaces) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"old\"] = 1;\n"
      "    aa = '{\"x\":5, \"y\":9};\n"
      "    result = aa[\"y\"] + aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 11u);
}

TEST(AssocLiteral, RuntimeLiteralDefaultGovernsMissingRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa = '{5:50, default:77};\n"
      "    result = aa[999];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

TEST(AssocLiteral, DeclDefaultOnlyReturnsDefaultOnMissingRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:99};\n"
      "  int result;\n"
      "  initial result = aa[7];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

TEST(AssocLiteral, DefaultReadIntKeyIssuesNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[int] = '{1:10, default:77};\n"
      "  int result;\n"
      "  initial result = aa[999];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AssocLiteral, DefaultReadStringKeyIssuesNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[string] = '{\"a\":10, default:55};\n"
      "  int result;\n"
      "  initial result = aa[\"missing\"];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AssocLiteral, MissingReadNoDefaultIntKeyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{1:10};\n"
      "  int result;\n"
      "  initial result = aa[999];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocLiteral, MissingReadNoDefaultStringKeyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string] = '{\"a\":1};\n"
      "  int result;\n"
      "  initial result = aa[\"b\"];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocLiteral, MissingReadNoDefault4StateReturnsX) {
  auto v = RunAndGet(
      "module t;\n"
      "  integer aa[int] = '{1:10};\n"
      "  int result;\n"
      "  initial result = $isunknown(aa[999]);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocLiteral, DefaultDoesNotAffectNum) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{1:10, 2:20, default:99};\n"
      "  int result;\n"
      "  initial result = aa.num();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocLiteral, DefaultDoesNotAffectSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{5:50, default:0};\n"
      "  int result;\n"
      "  initial result = aa.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocLiteral, DefaultDoesNotAffectExistsMissing) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{1:10, default:99};\n"
      "  int result;\n"
      "  initial result = aa.exists(999);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocLiteral, DefaultDoesNotAffectFirst) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.first(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(AssocLiteral, DefaultDoesNotAffectLast) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.last(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocLiteral, DefaultDoesNotAffectNext) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.first(k);\n"
      "    d = aa.next(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocLiteral, DefaultDoesNotAffectPrev) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.last(k);\n"
      "    d = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(AssocLiteral, DefaultDoesNotAffectDelete) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa.delete(10);\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

}  // namespace
