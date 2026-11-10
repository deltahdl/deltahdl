#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"

using namespace delta;

namespace {

TEST(DynamicArrayNewSimulation, NewAllocatesWithSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArrayNewSimulation, NewDefaultInitializesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    result = d[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewZeroSizeCreatesEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[0];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewWithInitCopiesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, NewWithInitTruncates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30, 40};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[2](src);\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(DynamicArrayNewSimulation, NewWithInitTruncatesKeepsLeadingElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30, 40};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[2](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, NewWithInitPads) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[5](src);\n"
      "    result = d[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewWithInitPreservesOnPad) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[5](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, SelfReferenceResize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DynamicArrayNewSimulation, SelfReferenceResizeNewSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

TEST(DynamicArrayNewSimulation, NewNegativeSizeIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = -1;\n"
      "    d = new[n];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 6,
                            "7.5.1"));
}

TEST(DynamicArrayNewSimulation, SelfReferenceResizePadZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d[4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewSizeFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int N = 3;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[N];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DynamicArrayNewSimulation, NewNonIntElementTypeCopiesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] src[] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  logic [7:0] d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[2](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xBBu);
}

TEST(DynamicArrayNewSimulation, DeclNewSizesArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[4];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArrayNewSimulation, DeclNewDefaultInitializesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[4];\n"
      "  int result;\n"
      "  initial result = d[2];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, DeclNewWithInitCopiesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int d[] = new[3](src);\n"
      "  int result;\n"
      "  initial result = d[1];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, DeclNewNegativeSizeIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = new[-1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 2,
                            "7.5.1"));
}

TEST(DynamicArrayNewSimulation, ProceduralNegativeSizeNames7_5_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = -3;\n"
      "    d = new[n];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 6,
                            "7.5.1"));
}

TEST(DynamicArrayNewSimulation, DeclNegativeSizeNames7_5_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = new[-2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 2,
                            "7.5.1"));
}

void ExpectDefaultElementsOwnWords(const QueueObject* q, size_t n) {
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), n);
  for (size_t i = 0; i < n; ++i) {
    SCOPED_TRACE(testing::Message() << "element " << i);
    ASSERT_NE(q->elements[i].words, nullptr);
    EXPECT_EQ(q->elements[i].ToUint64(), 0u);
    for (size_t j = 0; j < i; ++j)
      EXPECT_NE(q->elements[i].words, q->elements[j].words)
          << "shares a buffer with element " << j;
  }
}

void ExpectElementsCopiedOwningWords(const QueueObject* src,
                                     const QueueObject* dst,
                                     const std::vector<uint64_t>& expected) {
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  ASSERT_EQ(src->elements.size(), expected.size());
  ASSERT_EQ(dst->elements.size(), expected.size());
  for (size_t i = 0; i < expected.size(); ++i) {
    SCOPED_TRACE(testing::Message() << "element " << i);
    ASSERT_NO_FATAL_FAILURE(
        ExpectOwnWordsCopy(src->elements[i], dst->elements[i]));
    EXPECT_EQ(dst->elements[i].ToUint64(), expected[i]);
  }
}

TEST(DynamicArrayNewSimulation, NewWithoutInitGivesEachElementItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  initial d = new[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(
      ExpectDefaultElementsOwnWords(f.ctx.FindQueue("d"), 3u));
}

TEST(DynamicArrayNewSimulation, NewWithInitGivesDestinationItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int s[];\n"
      "  int d[];\n"
      "  initial begin\n"
      "    s = new[2];\n"
      "    s[0] = 32'h1234_5678;\n"
      "    s[1] = 32'h0BAD_F00D;\n"
      "    d = new[2](s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(ExpectElementsCopiedOwningWords(
      f.ctx.FindQueue("s"), f.ctx.FindQueue("d"), {0x12345678u, 0x0BADF00Du}));
}

TEST(DynamicArrayNewSimulation, DeclNewWithoutInitGivesEachElementItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = new[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(
      ExpectDefaultElementsOwnWords(f.ctx.FindQueue("d"), 3u));
}

TEST(DynamicArrayNewSimulation, DeclNewWithInitGivesDestinationItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int s[] = '{32'h1234_5678, 32'h0BAD_F00D};\n"
      "  int d[] = new[2](s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(ExpectElementsCopiedOwningWords(
      f.ctx.FindQueue("s"), f.ctx.FindQueue("d"), {0x12345678u, 0x0BADF00Du}));
}

TEST(DynamicArrayNewSimulation, NewCopiesAFixedArrayInitializer) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int isrc[3] = '{5, 6, 7};\n"
      "  int a[], b[], c[];\n"
      "  initial begin\n"
      "    a = new[3](isrc); b = new[2](isrc); c = new[4](isrc);\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", a[0], a[2], b.size(),\n"
      "             b[1], c[2], c[3]);\n"
      "    c = new[4];\n"
      "    $display(\"%0d %0d\", c.size(), c[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 7 2 6 7 0\n4 0\n");
}

TEST(DynamicArrayNewSimulation, NewFillsA4StateArrayWithX) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  logic [3:0] lda[];\n"
      "  bit [3:0] bda[];\n"
      "  function void init(); lda = new[2]; bda = new[2]; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic [3:0] lda[];\n"
      "  bit [3:0] bda[];\n"
      "  C c = new;\n"
      "  initial begin\n"
      "    lda = new[2]; bda = new[2]; c.init();\n"
      "    $display(\"%b %0d %0d %b %0d %0d\", lda[1], $isunknown(lda),\n"
      "             $isunknown(bda), c.lda[0], $isunknown(c.lda),\n"
      "             $isunknown(c.bda));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xxxx 1 0 xxxx 1 0\n");
}

TEST(DynamicArrayNewSimulation, NewSizesADynamicSubarrayOfAFixedArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int arr[2][][];\n"
      "  initial begin\n"
      "    arr[0] = new[4];\n"
      "    arr[0][0] = new[2];\n"
      "    arr[0][0][1] = 77;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", arr[0].size(), arr[0][0].size(),\n"
      "             arr[0][0][1], arr[0][1].size(), arr[1].size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 2 77 0 0\n");
}

TEST(DynamicArrayNewSimulation,
     NewSizesADynamicArrayOfFixedArraysInAFixedArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int a[3][][5];\n"
      "  initial begin\n"
      "    a[2] = new[4];\n"
      "    a[2][1][3] = 7;\n"
      "    $display(\"%0d %0d %0d %0d\", a[2][1][3], $size(a), a[2].size(),\n"
      "             a[0].size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 3 4 0\n");
}

TEST(DynamicArrayNewSimulation, NewSizesAMultiDimFixedElementOfAFixedArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int b[2][][2][3:1];\n"
      "  initial begin\n"
      "    b[1] = new[2];\n"
      "    b[1][1][0][1] = 9;\n"
      "    b[1][1][1][3] = 4;\n"
      "    $display(\"%0d %0d %0d %0d\", b[1][1][0][1], b[1][1][1][3],\n"
      "             b[1][1][0][2], b[1].size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 4 0 2\n");
}

TEST(DynamicArrayNewSimulation, NewSizesEachElementOfAnArrayOfDynamicArrays) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int d[][];\n"
      "  int fx[2][];\n"
      "  initial begin\n"
      "    int l[][];\n"
      "    d = new[3]; d[1] = new[2]; d[2] = new[5]; d[1][1] = 9;\n"
      "    fx[1] = new[3]; fx[1][2] = 6;\n"
      "    l = new[2]; l[0] = new[4]; l[0][3] = 8;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", d.size(), d[0].size(), "
      "d[1].size(),\n"
      "             d[2].size(), d[1][1]);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", fx[0].size(), fx[1].size(), "
      "fx[1][2],\n"
      "             l[0].size(), l[0][3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 0 2 5 9\n0 3 6 4 8\n");
}

TEST(DynamicArrayNewSimulation, UnsignedSizeWithTopBitSetIsNotNegative) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C; int d[]; endclass\n"
      "  bit [3:0] n = 4'd8;\n"
      "  int a[] = new[4'd8];\n"
      "  int b[];\n"
      "  C c;\n"
      "  initial begin\n"
      "    b = new[n];\n"
      "    c = new;\n"
      "    c.d = new[n];\n"
      "    $display(\"%0d %0d %0d\", a.size(), b.size(), c.d.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 8 8\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DynamicArrayNewSimulation,
     ClauseArr1AndArr2DeclarationsSizeTheOuterArray) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int arr1 [][2][3] = new [4]; int arr2 [][] = new [4];\n"
                 "  initial $display(\"%0d %0d %0d %0d\", arr1.size(), "
                 "arr1[3][1][2], arr2.size(), arr2[0].size());\n"
                 "endmodule\n",
                 f),
      "4 0 4 0\n");
}

TEST(DynamicArrayNewSimulation,
     DISABLED_NewThroughAnUncreatedElementCreatesNothing) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int arr [2][][];\n"
                       "  initial begin\n"
                       "    arr[0] = new [4]; arr[0][0] = new [2];\n"
                       "    arr[1][0] = new [2];\n"
                       "    $display(\"%0d %0d %0d\", arr[1].size(), "
                       "arr[0].size(), arr[0][0].size());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 4 2\n");
}

TEST(DynamicArrayNewSimulation, SizeIsEvaluatedBeforeTheInitializer) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  string log; int n = 2; int src [3] = '{4, 5, 6};\n"
                 "  function automatic int f(); log = {log, \"f\"}; return n; "
                 "endfunction\n"
                 "  typedef int a3_t [3];\n"
                 "  function automatic a3_t g();\n"
                 "    log = {log, \"g\"}; n = 3; return src;\n"
                 "  endfunction\n"
                 "  int d [];\n"
                 "  initial begin\n"
                 "    d = new[f()](g());\n"
                 "    $display(\"%s %0d\", log, d.size());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "fg 2\n");
}

TEST(DynamicArrayNewSimulation, DISABLED_DeclarationSizeFromAFunctionCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string log; int src [3] = '{4, 5, 6};\n"
                       "  function automatic int f(); log = {log, \"f\"}; "
                       "return 2; endfunction\n"
                       "  int d [] = new[f()](src);\n"
                       "  initial #1 $display(\"%s %0d %0d\", log, d.size(), "
                       "d[1]);\n"
                       "endmodule\n",
                       f),
            "f 2 5\n");
}

TEST(DynamicArrayNewSimulation,
     DISABLED_InitializerFromAFunctionCallOrADeclarationPattern) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int src [3] = '{4, 5, 6};\n"
                 "  typedef int a3_t [3];\n"
                 "  function automatic a3_t g(); return src; endfunction\n"
                 "  int p [] = new[2]('{7, 8, 9});\n"
                 "  int d [];\n"
                 "  initial begin\n"
                 "    d = new[2](g());\n"
                 "    $display(\"%0d %0d %0d %0d\", d[1], d.size(), p[1], "
                 "p.size());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "5 2 8 2\n");
}

TEST(DynamicArrayNewSimulation,
     NewWithoutAnInitializerDiscardsEarlierElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int d []; logic [7:0] l [];\n"
                       "  initial begin\n"
                       "    d = new[3]; d[0] = 5; d[2] = 7; d = new[3];\n"
                       "    $display(\"%0d %0d\", d[0], d[2]);\n"
                       "    d[1] = 4; d = new[5];\n"
                       "    $display(\"%0d %0d %0d\", d[1], d[4], d.size());\n"
                       "    l = new[2]; l[1] = 1; l = new[4];\n"
                       "    $display(\"%b %b %b\", l[0], l[1], l[3]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 0\n0 0 5\nxxxxxxxx xxxxxxxx xxxxxxxx\n");
}

TEST(DynamicArrayNewSimulation, RefToAnElementOutdatedByNewWritesNothing) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int d [];\n"
                       "  task automatic tk(ref int r); d = new[3]; r = 9; "
                       "endtask\n"
                       "  initial begin\n"
                       "    d = new[3]; d[1] = 4; tk(d[1]);\n"
                       "    $display(\"%0d %0d\", d[1], d.size());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 3\n");
}

}  // namespace
