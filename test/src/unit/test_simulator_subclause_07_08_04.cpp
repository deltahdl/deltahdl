#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(IntegralIndexAssocArraySimulation, WriteAndReadEndToEnd) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int aa[int];\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    aa[5] = 42;\n"
                      "    result = aa[5];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(IntegralIndexAssocArraySimulation, SignedIndexCastAndOrdering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit signed [4:1] SNibble;\n"
      "  int aa[SNibble];\n"
      "  initial begin\n"
      "    aa[3] = 100;\n"
      "    aa[12] = 200;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  ASSERT_EQ(aa->int_data.size(), 2u);
  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, -4);
  EXPECT_EQ(it->second.ToUint64(), 200u);
  ++it;
  EXPECT_EQ(it->first, 3);
  EXPECT_EQ(it->second.ToUint64(), 100u);
}

TEST(IntegralIndexAssocArraySimulation, UnsignedIndexCastAndOrdering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [4:1] UNibble;\n"
      "  int aa[UNibble];\n"
      "  initial begin\n"
      "    aa[3] = 100;\n"
      "    aa[12] = 200;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  ASSERT_EQ(aa->int_data.size(), 2u);
  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, 3);
  EXPECT_EQ(it->second.ToUint64(), 100u);
  ++it;
  EXPECT_EQ(it->first, 12);
  EXPECT_EQ(it->second.ToUint64(), 200u);
}

TEST(IntegralIndexAssocArraySimulation, SignedByteSignExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit signed [7:0] SByte;\n"
      "  int aa[SByte];\n"
      "  initial aa[200] = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_EQ(aa->int_data.count(-56), 1u);
  EXPECT_EQ(aa->int_data.count(200), 0u);
}

TEST(IntegralIndexAssocArraySimulation, UnsignedByteZeroExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [7:0] UByte;\n"
      "  int aa[UByte];\n"
      "  initial aa[200] = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_EQ(aa->int_data.count(200), 1u);
  EXPECT_EQ(aa->int_data.count(-56), 0u);
}

TEST(IntegralIndexAssocArraySimulation, IndexTruncatedToWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [4:1] UNibble;\n"
      "  int aa[UNibble];\n"
      "  initial begin\n"
      "    aa[3] = 1;\n"
      "    aa[19] = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_EQ(aa->Size(), 1u);
  ASSERT_EQ(aa->int_data.count(3), 1u);
  EXPECT_EQ(aa->int_data.at(3).ToUint64(), 2u);
}

TEST(IntegralIndexAssocArraySimulation, UnsignedCastReadRoundtrip) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef bit [7:0] UByte;\n"
                      "  int aa[UByte];\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    aa[200] = 99;\n"
                      "    result = aa[200];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(IntegralIndexAssocArraySimulation, SignedNegativeKeyRoundtrip) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int aa[int];\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    aa[-3] = 77;\n"
                      "    result = aa[-3];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            77u);
}

TEST(IntegralIndexAssocArraySimulation, XZIndexInvalidWrite) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  initial aa[8'bxx] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_TRUE(aa->int_data.empty());
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(IntegralIndexAssocArraySimulation, XZIndexInvalidRead) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    result = aa[8'bxx];\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(IntegralIndexAssocArraySimulation, ExplicitRealCastIndexEndToEnd) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int aa[int];\n"
                      "  real r;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    r = 3.0;\n"
                      "    aa[int'(r)] = 55;\n"
                      "    result = aa[3];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(IntegralIndexAssocArraySimulation, SignedBuiltinIntOrdering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  initial begin\n"
      "    aa[10] = 1;\n"
      "    aa[-5] = 2;\n"
      "    aa[3] = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  ASSERT_EQ(aa->int_data.size(), 3u);
  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, -5);
  ++it;
  EXPECT_EQ(it->first, 3);
  ++it;
  EXPECT_EQ(it->first, 10);
}

TEST(IntegralIndexAssocArraySimulation, IntegerVariableXZIndexInvalid) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  initial begin\n"
      "    idx = 2'bxx;\n"
      "    aa[idx] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_TRUE(aa->int_data.empty());
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(IntegralIndexAssocArraySimulation, FunctionBodyWriteKeyMatchesModuleRead) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef bit [3:0] Nibble;\n"
                      "  int aa[Nibble];\n"
                      "  int result;\n"
                      "  int called;\n"
                      "  function automatic int store(int v);\n"
                      "    aa[-1] = v;\n"
                      "    return v;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    called = store(42);\n"
                      "    result = aa[-1];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(IntegralIndexAssocArraySimulation,
     FunctionBodyAndModuleWritesShareOneKey) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef bit [3:0] Nibble;\n"
                      "  int aa[Nibble];\n"
                      "  int result;\n"
                      "  int called;\n"
                      "  function automatic int store(int v);\n"
                      "    aa[-1] = v;\n"
                      "    return v;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    called = store(1);\n"
                      "    aa[15] = 2;\n"
                      "    result = aa.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(IntegralIndexAssocArraySimulation,
     InlinePackedDimensionIndexSharesOneKey) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int aa[bit[3:0]];\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    aa[-1] = 1;\n"
                      "    aa[15] = 2;\n"
                      "    result = aa.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(IntegralIndexAssocArraySimulation,
     SignedIndexTypesOrderNegativeKeysFirst) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit signed [4:1] SNibble;\n"
      "  typedef bit [4:1] UNibble;\n"
      "  int s[SNibble], u[UNibble], b[byte];\n"
      "  SNibble sk; UNibble uk; byte bk;\n"
      "  initial begin\n"
      "    s[5] = 1; s[-3] = 2; s[0] = 3;\n"
      "    u[2] = 1; u[-1] = 2;\n"
      "    b[5] = 1; b[-3] = 2;\n"
      "    void'(s.first(sk)); $write(\"%0d\", sk);\n"
      "    void'(s.last(sk)); $write(\" %0d\", sk);\n"
      "    void'(u.last(uk)); $write(\" %0d\", uk);\n"
      "    void'(b.first(bk)); $display(\" %0d\", bk);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 5 15 -3\n");
}

TEST(IntegralIndexAssocArraySimulation, IndexIsKeyedAndOrderedByItsWholeValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int w [bit [99:0]];\n"
      "  int u [bit [63:0]];\n"
      "  int s [longint];\n"
      "  int sw [bit signed [99:0]];\n"
      "  bit [99:0] kw;\n"
      "  bit [63:0] k;\n"
      "  longint ks;\n"
      "  bit signed [99:0] kws;\n"
      "  initial begin\n"
      "    w[100'h1_0000_0000_0000_0000] = 1;\n"
      "    w[100'h2_0000_0000_0000_0000] = 2;\n"
      "    w[5] = 3;\n"
      "    u[64'h8000_0000_0000_0000] = 1;\n"
      "    u[1] = 2;\n"
      "    s[1] = 1;\n"
      "    s[-1] = 2;\n"
      "    sw[-1] = 1;\n"
      "    sw[{100{1'b1}} << 64] = 2;\n"
      "    $display(\"%0d %0d %0d\", w.num(), w[100'h2_0000_0000_0000_0000],\n"
      "             w.exists(100'h3_0000_0000_0000_0000));\n"
      "    void'(w.last(kw));\n"
      "    $display(\"%0d\", kw);\n"
      "    void'(w.prev(kw));\n"
      "    $display(\"%0d\", kw);\n"
      "    void'(u.first(k));\n"
      "    $display(\"%0h\", k);\n"
      "    void'(u.next(k));\n"
      "    $display(\"%0h\", k);\n"
      "    void'(s.first(ks));\n"
      "    $display(\"%0d\", ks);\n"
      "    void'(sw.first(kws));\n"
      "    $display(\"%0d\", kws);\n"
      "    void'(sw.next(kws));\n"
      "    $display(\"%0d\", kws);\n"
      "    foreach (w[i]) $display(\"%0d\", i);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "3 2 0\n"
            "36893488147419103232\n"
            "18446744073709551616\n"
            "1\n"
            "8000000000000000\n"
            "-1\n"
            "-18446744073709551616\n"
            "-1\n"
            "5\n"
            "18446744073709551616\n"
            "36893488147419103232\n");
}

TEST(IntegralIndexAssocArraySimulation, APackedIndexKeysAClassPropertyWhole) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  bit [7:0] m[bit [79:0]];\n"
      "endclass\n"
      "module t;\n"
      "  function automatic int count();\n"
      "    bit [7:0] a[bit [79:0]];\n"
      "    a[80'h1_0000_0000_0000_0005] = 2; a[5] = 1;\n"
      "    return a.num() * 100 + a[5] * 10 + a[80'h1_0000_0000_0000_0005];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.m[80'h1_0000_0000_0000_0005] = 2;\n"
      "    c.m[5] = 1;\n"
      "    $display(\"%0d %0d %0d %0d\", c.m.num(), c.m[5],\n"
      "             c.m[80'h1_0000_0000_0000_0005], count());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1 2 212\n");
}

}  // namespace
