#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BitStreamCastSim, BitStreamArrayToInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hDE;\n"
      "    arr[1] = 8'hAD;\n"
      "    arr[2] = 8'hBE;\n"
      "    arr[3] = 8'hEF;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(BitStreamCastSim, BitStreamShortArrayToInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 16'hCAFE;\n"
      "    arr[1] = 16'hBABE;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xCAFEBABEu);
}

TEST(BitStreamCastSim, BitStreamStructRoundTrip) {
  SimFixture f;
  auto* p2 = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  int flat;\n"
      "  pair_t p2;\n"
      "  initial begin\n"
      "    p = 16'hCAFE;\n"
      "    flat = int'(p);\n"
      "    p2 = pair_t'(flat);\n"
      "  end\n"
      "endmodule\n",
      f, "p2");
  ASSERT_NE(p2, nullptr);
  EXPECT_EQ(p2->value.ToUint64(), 0xCAFEu);
}

TEST(BitStreamCastSim, SingleElementArrayCast) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte arr [1];\n"
      "  byte result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAB;\n"
      "    result = byte'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(BitStreamCastSim, IntArrayElementIsPackedWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int arr [1];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 32'h8BAD_F00D;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x8BADF00Du);
}

TEST(BitStreamCastSim, TwoIntArrayElementsFillASixtyFourBitType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [63:0] u64_t;\n"
      "  int arr [2];\n"
      "  u64_t result;\n"
      "  initial begin\n"
      "    arr[0] = 32'hDEAD_BEEF;\n"
      "    arr[1] = 32'hCAFE_F00D;\n"
      "    result = u64_t'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFCAFEF00Dull);
}

TEST(BitStreamCastSim, LongintArrayElementIsPackedWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  longint arr [1];\n"
      "  longint result;\n"
      "  initial begin\n"
      "    arr[0] = 64'hDEAD_BEEF_CAFE_F00D;\n"
      "    result = longint'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFCAFEF00Dull);
}

TEST(BitStreamCastSim, TwoIntQueueElementsFillASixtyFourBitType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [63:0] u64_t;\n"
      "  int q [$];\n"
      "  u64_t result;\n"
      "  initial begin\n"
      "    q.push_back(32'hDEAD_BEEF);\n"
      "    q.push_back(32'hCAFE_F00D);\n"
      "    result = u64_t'(q);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFCAFEF00Dull);
}

TEST(BitStreamCastSim, TwoIntAssocElementsFillASixtyFourBitType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [63:0] u64_t;\n"
      "  int amap [int];\n"
      "  u64_t result;\n"
      "  initial begin\n"
      "    amap[1] = 32'hCAFE_F00D;\n"
      "    amap[0] = 32'hDEAD_BEEF;\n"
      "    result = u64_t'(amap);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFCAFEF00Dull);
}

TEST(BitStreamCastSim, BitStreamSourceFourStatePropagates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef logic [15:0] w16_t;\n"
      "  logic [7:0] arr [2];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'b1010_xxxx;\n"
      "    arr[1] = 8'h55;\n"
      "    result = w16_t'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_GT(var->value.nwords, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(BitStreamCastSim, BitStreamQueueSourceToIntPacksIndexZeroInMsb) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte q [$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(8'hDE);\n"
      "    q.push_back(8'hAD);\n"
      "    q.push_back(8'hBE);\n"
      "    q.push_back(8'hEF);\n"
      "    result = int'(q);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(BitStreamCastSim, BitStreamQueueSourceFourStatePropagates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef logic [15:0] w16_t;\n"
      "  logic [7:0] q [$];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    q.push_back(8'b1010_xxxx);\n"
      "    q.push_back(8'h55);\n"
      "    result = w16_t'(q);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_GT(var->value.nwords, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(BitStreamCastSim, FourStateSourceIntoTwoStateDestStripsUnknown) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [2];\n"
      "  shortint result;\n"
      "  initial begin\n"
      "    arr[0] = 8'b1010_xxxx;\n"
      "    arr[1] = 8'h55;\n"
      "    result = shortint'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_GT(var->value.nwords, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0x55u);
}

TEST(BitStreamCastSim, BitStreamDynamicArraySourceToIntPacksIndexZeroInMsb) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte d [];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    d[0] = 8'hDE;\n"
      "    d[1] = 8'hAD;\n"
      "    d[2] = 8'hBE;\n"
      "    d[3] = 8'hEF;\n"
      "    result = int'(d);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(BitStreamCastSim, BitStreamQueueSourceToPackedStruct) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  byte q [$];\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    q.push_back(8'hCA);\n"
      "    q.push_back(8'hFE);\n"
      "    p = pair_t'(q);\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

TEST(BitStreamCastSim, BitStreamAssocSourcePacksInIndexSortedOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte amap [int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    amap[3] = 8'hEF;\n"
      "    amap[1] = 8'hAD;\n"
      "    amap[0] = 8'hDE;\n"
      "    amap[2] = 8'hBE;\n"
      "    result = int'(amap);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(BitStreamCastSim, CastToAnUnpackedArrayTypedefFillsItsElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef bit B8 [8:1];\n"
                       "  typedef byte P [2];\n"
                       "  B8 e;\n"
                       "  P p;\n"
                       "  byte x;\n"
                       "  shortint h = 16'hA5C3;\n"
                       "  initial begin\n"
                       "    x = 8'h81;\n"
                       "    e = B8'(x);\n"
                       "    p = P'(h);\n"
                       "    $display(\"%0d %0d %0d %h %h\", e[8], e[1], e[7], "
                       "p[0], p[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1 0 a5 c3\n");
}

TEST(BitStreamCastSim, CastIntoAStructWithAnUnpackedArrayMember) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef struct {\n"
                 "    shortint address; logic [3:0] code; byte command [2];\n"
                 "  } Control;\n"
                 "  typedef bit [35:0] b36_t;\n"
                 "  Control q;\n"
                 "  bit [35:0] v, back;\n"
                 "  initial begin\n"
                 "    v = 36'hFFFEA1122;\n"
                 "    q = Control'(v);\n"
                 "    back = b36_t'(q);\n"
                 "    $display(\"%h %h %h %h %h\", q.address, q.code, "
                 "q.command[0], q.command[1], back);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "fffe a 11 22 fffea1122\n");
}

TEST(BitStreamCastSim, CastIntoAStructGivesItsStringMemberTheRemainingBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int n; string s;} pair_t;\n"
                       "  typedef struct {string s; string t;} in_t;\n"
                       "  typedef struct {byte b; in_t i;} two_t;\n"
                       "  pair_t p;\n"
                       "  two_t w;\n"
                       "  bit [47:0] v = {32'd7, \"hi\"};\n"
                       "  bit [23:0] u = 24'h414243;\n"
                       "  initial begin\n"
                       "    p = pair_t'(v);\n"
                       "    w = two_t'(u);\n"
                       "    $display(\"%0d [%s] %h [%s] [%s]\", p.n, p.s, w.b, "
                       "w.i.s, w.i.t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7 [hi] 41 [BC] []\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BitStreamCastSim, CastIntoAStructWithAStringOfNoWholeBytesIsAnError) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  pair_t p, q;\n"
      "  bit [43:0] v = 44'h1;\n"
      "  bit [15:0] h = 16'h1;\n"
      "  initial begin\n"
      "    p = pair_t'(v);\n"
      "    q = pair_t'(h);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'pair_t': the 44-bit source "
                            "leaves its first dynamically sized member 12 "
                            "bits, which are no whole number of its 8-bit "
                            "elements",
                            7, "6.24.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'pair_t': the 16-bit source "
                            "is narrower than the 32 bits of its fixed-size "
                            "members",
                            8, "6.24.3"));
}

TEST(BitStreamCastSim, CastFromAStructStreamsItsStringMemberAsBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int n; string s;} pair_t;\n"
                       "  typedef struct {string s; string t;} in_t;\n"
                       "  typedef struct {byte b; in_t i;} two_t;\n"
                       "  typedef bit [47:0] b48_t;\n"
                       "  typedef bit [23:0] b24_t;\n"
                       "  pair_t p = '{7, \"hi\"};\n"
                       "  two_t w = '{8'h41, '{\"BC\", \"\"}};\n"
                       "  initial $display(\"%h %h\", b48_t'(p), b24_t'(w));\n"
                       "endmodule\n",
                       f),
            "000000076869 414243\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BitStreamCastSim, CastFromAStructOfAnotherStreamedSizeIsAnError) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  typedef bit [39:0] b40_t;\n"
      "  pair_t p = '{7, \"hi\"};\n"
      "  b40_t b;\n"
      "  initial b = b40_t'(p);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'b40_t': the source streams "
                            "48 bits, where the type holds 40",
                            6, "6.24.3"));
}

TEST(BitStreamCastSim, CastFromAStructStreamsItsDynamicArrayMemberElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; byte d[];} dyn_t;\n"
                       "  typedef bit [23:0] b24_t;\n"
                       "  typedef bit [7:0] b8_t;\n"
                       "  dyn_t s, e;\n"
                       "  initial begin\n"
                       "    s.b = 8'h41; e.b = 8'h44;\n"
                       "    s.d = new[2];\n"
                       "    s.d[0] = 8'h42; s.d[1] = 8'h43;\n"
                       "    $display(\"%h %h\", b24_t'(s), b8_t'(e));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "414243 44\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BitStreamCastSim, CastIntoAStructGivesItsDynamicArrayMemberTheRemainder) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; byte d[];} dyn_t;\n"
                       "  dyn_t s;\n"
                       "  bit [23:0] v = 24'h414243;\n"
                       "  initial begin\n"
                       "    s = dyn_t'(v);\n"
                       "    $display(\"%h %0d %h %h\", s.b, s.d.size(), "
                       "s.d[0], s.d[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "41 2 42 43\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BitStreamCastSim, CastIntoAStructOfNoWholeDynamicElementsIsAnError) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {byte b; int d[];} ints_t;\n"
      "  ints_t s;\n"
      "  bit [55:0] v = 56'h1;\n"
      "  initial s = ints_t'(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'ints_t': the 56-bit source "
                            "leaves its first dynamically sized member 48 "
                            "bits, which are no whole number of its 32-bit "
                            "elements",
                            5, "6.24.3"));
}

TEST(BitStreamCastSim, AStringArrayMemberStreamsEachElementAsBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; string v [2];} names_t;\n"
                       "  typedef bit [31:0] b32_t;\n"
                       "  names_t m, n;\n"
                       "  bit [23:0] u = 24'h414243;\n"
                       "  initial begin\n"
                       "    m.b = 8'h41; m.v[0] = \"B\"; m.v[1] = \"CD\";\n"
                       "    n = names_t'(u);\n"
                       "    $display(\"%h %h [%s] [%s] %0d\", b32_t'(m), n.b, "
                       "n.v[0], n.v[1], n.v[0].len());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "41424344 41 [BC] [] 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BitStreamCastSim, CastFromAStructStreamsItsDynamicStringElementsAsBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; string d[];} names_t;\n"
                       "  typedef bit [31:0] b32_t;\n"
                       "  names_t m;\n"
                       "  initial begin\n"
                       "    m.b = 8'h41;\n"
                       "    m.d = new[3];\n"
                       "    m.d[0] = \"B\"; m.d[2] = \"CD\";\n"
                       "    $display(\"%h\", b32_t'(m));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "41424344\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BitStreamCastSim, CastIntoAStructGivesItsDynamicStringArrayOneString) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; string d[];} names_t;\n"
                       "  names_t m, e;\n"
                       "  bit [31:0] v = 32'h41424344;\n"
                       "  bit [7:0] h = 8'h45;\n"
                       "  initial begin\n"
                       "    m = names_t'(v);\n"
                       "    e = names_t'(h);\n"
                       "    $display(\"%h %0d [%s] %h %0d\", m.b, m.d.size(), "
                       "m.d[0], e.b, e.d.size());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "41 1 [BCD] 45 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BitStreamCastSim, CastIntoAStructOfNoWholeDynamicStringBytesIsAnError) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {byte b; string d[];} names_t;\n"
      "  names_t m;\n"
      "  bit [27:0] v = 28'h1;\n"
      "  initial m = names_t'(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'names_t': the 28-bit source "
                            "leaves its first dynamically sized member 20 "
                            "bits, which are no whole number of its 8-bit "
                            "elements",
                            5, "6.24.3"));
}

}  // namespace
