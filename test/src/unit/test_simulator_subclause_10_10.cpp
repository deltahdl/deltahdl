#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Expr* MakeConcat(Arena& arena, std::vector<Expr*> elems) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  e->elements = std::move(elems);
  return e;
}

TEST(UnpackedArrayConcatSim, LeftToRightArrangement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[1:3];\n"
      "  initial A = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a1 = f.ctx.FindVariable("A[1]");
  auto* a2 = f.ctx.FindVariable("A[2]");
  auto* a3 = f.ctx.FindVariable("A[3]");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  ASSERT_NE(a3, nullptr);
  EXPECT_EQ(a1->value.ToUint64(), 10u);
  EXPECT_EQ(a2->value.ToUint64(), 20u);
  EXPECT_EQ(a3->value.ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, EmptyConcatClearsQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->elements.empty());
}

TEST(UnpackedArrayConcatSim, ConcatToQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, ConcatWithArrayItemsExpandsLeftToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[0:1] = '{10, 20};\n"
      "  int B[0:1] = '{30, 40};\n"
      "  int q[$];\n"
      "  initial q = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

TEST(UnpackedArrayConcatSim, DescendingArrayItemExpandsHighestIndexFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[1:0];\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    A[1] = 10;\n"
      "    A[0] = 20;\n"
      "    q = {A};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(UnpackedArrayConcatSim, ConcatToDynamicArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  initial d = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("d");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, EmptyConcatToFixedSizeError) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_descending = false;
  f.ctx.RegisterArray("A", info);
  for (uint32_t i = 0; i < 3; ++i)
    f.ctx.CreateVariable("A[" + std::to_string(i) + "]", 32);
  auto* rhs = MakeConcat(f.arena, {});
  auto* stmt = MakeAssign(f.arena, "A", rhs);
  TryArrayAggregateAssign(stmt, f.ctx, f.arena);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 3 elements, got 0",
                            0, "10.10"));
}

TEST(UnpackedArrayConcatSim, FixedSizeMismatchFromSourceErrorsAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 3 elements, got 4",
                            3, "10.10"));
}

TEST(UnpackedArrayConcatSim, BoundedQueueOverflowFromSourceTruncatesAndWarns) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$:1];\n"
      "  initial q = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto warnings_before = f.diag.WarningCount();
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_GT(f.diag.WarningCount(), warnings_before);
}

TEST(UnpackedArrayConcatSim, BlockingSizeMismatchNames10_10) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[2];\n"
      "  initial A = {5, 6, 7};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch", 3,
                            "10.10"));
}

TEST(UnpackedArrayConcatSim, NonblockingSizeMismatchNames10_10) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int B[2];\n"
      "  initial B <= {8, 9, 10};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch", 3,
                            "10.10"));
}

TEST(UnpackedArrayConcatSim, ArrayItemGivesDestinationItsOwnElementWords) {
  SimFixture f;
  auto* a0 = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:1];\n"
      "  logic [7:0] b [0:1];\n"
      "  initial begin\n"
      "    a[0] = 8'hA5; a[1] = 8'h5A;\n"
      "    b = {a};\n"
      "  end\n"
      "endmodule\n",
      f, "a[0]");
  ASSERT_NE(a0, nullptr);
  auto* b0 = f.ctx.FindVariable("b[0]");
  ASSERT_NE(b0, nullptr);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(a0->value, b0->value));
  EXPECT_EQ(b0->value.words[0].aval, 0xA5u);
}

TEST(UnpackedArrayConcatSim, BracesAssignedToAQueueElementFillItsQueue) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef int q_t[$];\n"
      "  q_t fx[2];\n"
      "  q_t aa[string];\n"
      "  int qq[$][$];\n"
      "  initial begin\n"
      "    fx[0] = {1, 2};\n"
      "    aa[\"k\"] = {5};\n"
      "    qq.push_back({});\n"
      "    qq[0] = {qq[0], 5};\n"
      "    qq[0] = {qq[0], 6};\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", fx[0].size(), fx[0][1],\n"
      "             aa[\"k\"].size(), aa[\"k\"][0], qq[0].size(), qq[0][0],\n"
      "             qq[0][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 1 5 2 5 6\n");
}

TEST(UnpackedArrayConcatSim, ItemOfTheQueuesElementTypeIsOneElement) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][3];\n"
      "  int a[3] = '{1, 2, 3};\n"
      "  int s[$][$];\n"
      "  int b[$] = '{7, 8};\n"
      "  initial begin\n"
      "    r.push_back('{4, 5, 6});\n"
      "    r = {r, a};\n"
      "    r = {r, r[0]};\n"
      "    s = {b, b};\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", r.size(), r[0][2],\n"
      "             r[1][0], r[1][2], r[2][1], s.size(), s[1][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 6 1 3 5 2 8\n");
}

TEST(UnpackedArrayConcatSim, EachItemIsEvaluatedOnce) {
  const char* src =
      "module t;\n"
      "  int n = 0;\n"
      "  int A[2];\n"
      "  int a0, a1, calls;\n"
      "  function int f(); n++; return n; endfunction\n"
      "  initial begin A = {f(), f()}; a0 = A[0]; a1 = A[1]; calls = n; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a0"), 1u);
  EXPECT_EQ(RunAndGet(src, "a1"), 2u);
  EXPECT_EQ(RunAndGet(src, "calls"), 2u);
}

TEST(UnpackedArrayConcatSim, ASliceItemContributesItsElements) {
  const char* src =
      "module t;\n"
      "  int A[4] = '{1, 2, 3, 4};\n"
      "  int B[3];\n"
      "  int b0, b1, b2;\n"
      "  initial begin B = {A[1:2], A[0]}; b0 = B[0]; b1 = B[1]; b2 = B[2]; "
      "end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b0"), 2u);
  EXPECT_EQ(RunAndGet(src, "b1"), 3u);
  EXPECT_EQ(RunAndGet(src, "b2"), 1u);
}

TEST(UnpackedArrayConcatSim, AnItemOfTheElementTypeIsOneRow) {
  const char* src =
      "module t;\n"
      "  int M[2][3];\n"
      "  int R[3] = '{1, 2, 3};\n"
      "  int S[3] = '{4, 5, 6};\n"
      "  int m02, m10;\n"
      "  initial begin M = {R, S}; m02 = M[0][2]; m10 = M[1][0]; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "m02"), 3u);
  EXPECT_EQ(RunAndGet(src, "m10"), 4u);
}

TEST(UnpackedArrayConcatSim, ATypedStructurePatternItemIsOneElement) {
  const char* src =
      "typedef struct packed { byte a, b; } P;\n"
      "module t;\n"
      "  P arr[2];\n"
      "  int e0, e1;\n"
      "  initial begin\n"
      "    arr = {P'{8'h1, 8'h2}, P'{8'h3, 8'h4}};\n"
      "    e0 = arr[0]; e1 = arr[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "e0"), 0x0102u);
  EXPECT_EQ(RunAndGet(src, "e1"), 0x0304u);
}

TEST(UnpackedArrayConcatSim, ATypedArrayPatternItemFillsSeveralElements) {
  const char* src =
      "module t;\n"
      "  typedef int AI3[1:3];\n"
      "  int A5[1:5];\n"
      "  int a2, a4, a5;\n"
      "  initial begin\n"
      "    A5 = {1, AI3'{2, 3, 4}, 5};\n"
      "    a2 = A5[2]; a4 = A5[4]; a5 = A5[5];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a2"), 2u);
  EXPECT_EQ(RunAndGet(src, "a4"), 4u);
  EXPECT_EQ(RunAndGet(src, "a5"), 5u);
}

TEST(UnpackedArrayConcatSim, ANonblockingConcatenationExpandsATypedArrayItem) {
  const char* src =
      "module t;\n"
      "  typedef int AI3[1:3];\n"
      "  int A3[1:3] = '{1, 2, 3};\n"
      "  int A9[1:9];\n"
      "  int a5, a9;\n"
      "  initial begin\n"
      "    A9 <= {A3, 4, AI3'{5, 6, 7}, 8, 9};\n"
      "    #1 a5 = A9[5]; a9 = A9[9];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a5"), 5u);
  EXPECT_EQ(RunAndGet(src, "a9"), 9u);
}

TEST(UnpackedArrayConcatSim, ANonblockingConcatenationSizesADynamicArray) {
  const char* src =
      "module t;\n"
      "  int d[];\n"
      "  int n, d2;\n"
      "  initial begin d <= {1, 2, 3}; #1 n = d.size(); d2 = d[2]; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 3u);
  EXPECT_EQ(RunAndGet(src, "d2"), 3u);
}

TEST(UnpackedArrayConcatSim, ADeclarationInitializerExpandsAnArrayItem) {
  const char* src =
      "module t;\n"
      "  int A[2] = '{10, 20};\n"
      "  int B[4] = {A, 30, 40};\n"
      "  int q[$] = {A, 5};\n"
      "  int b0, b1, b3, n, q1;\n"
      "  initial begin b0 = B[0]; b1 = B[1]; b3 = B[3]; n = q.size(); q1 = "
      "q[1]; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b0"), 10u);
  EXPECT_EQ(RunAndGet(src, "b1"), 20u);
  EXPECT_EQ(RunAndGet(src, "b3"), 40u);
  EXPECT_EQ(RunAndGet(src, "n"), 3u);
  EXPECT_EQ(RunAndGet(src, "q1"), 20u);
}

TEST(UnpackedArrayConcatSim, ADeclarationInitializerOfTheWrongSizeIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int C[3] = {1, 2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 3 elements, got 2",
                            2, "10.10"));
}

TEST(UnpackedArrayConcatSim, ABracedPatternItemIsAConcatenationOverItsRow) {
  const char* src =
      "module t;\n"
      "  int A[2] = '{1, 2};\n"
      "  int C[2][2];\n"
      "  int c00, c01, c10, c11;\n"
      "  initial begin\n"
      "    C = '{{A}, {3, 4}};\n"
      "    c00 = C[0][0]; c01 = C[0][1]; c10 = C[1][0]; c11 = C[1][1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "c00"), 1u);
  EXPECT_EQ(RunAndGet(src, "c01"), 2u);
  EXPECT_EQ(RunAndGet(src, "c10"), 3u);
  EXPECT_EQ(RunAndGet(src, "c11"), 4u);
}

TEST(UnpackedArrayConcatSim, ABracedPatternItemOfTheWrongSizeIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int C[2][2];\n"
      "  initial C = '{{1}, {3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 2 elements, got 1",
                            3, "10.10"));
}

TEST(UnpackedArrayConcatSim, ContinuousAssignmentOfConcatToFixedArray) {
  const char* src =
      "module t;\n"
      "  int A[1:3]; int x = 5; int a1, a2, a3;\n"
      "  assign A = {10, x, 30};\n"
      "  initial begin\n"
      "    #1 x = 7;\n"
      "    #1 begin a1 = A[1]; a2 = A[2]; a3 = A[3]; end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a1"), 10u);
  EXPECT_EQ(RunAndGet(src, "a2"), 7u);
  EXPECT_EQ(RunAndGet(src, "a3"), 30u);
}

TEST(UnpackedArrayConcatSim,
     NullItemsForInterfaceClassAndVirtualInterfaceElements) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface class IC; endclass\n"
          "class K implements IC; endclass\n"
          "interface bus_if; logic v; endinterface\n"
          "module t;\n"
          "  bus_if b();\n"
          "  IC arr[2]; K k; virtual bus_if vifs[2];\n"
          "  initial begin\n"
          "    k = new; arr = {null, k};\n"
          "    vifs = {null, b};\n"
          "    $display(\"%b %b %b %b\", arr[0] == null, arr[1] != null,\n"
          "             vifs[0] == null, vifs[1] != null);\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 1 1 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnpackedArrayConcatSim, ReturnAndOutputArgumentTakeTheConcatenation) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef int i2_t [2];\n"
                       "typedef int iq_t [$];\n"
                       "module t;\n"
                       "  int a = 3, b = 4;\n"
                       "  function i2_t f(); return {a, b}; endfunction\n"
                       "  function iq_t g(); return {a, b, a}; endfunction\n"
                       "  task get(output int o[2]); o = {7, 8}; endtask\n"
                       "  int r[2], rq[$], oo[2];\n"
                       "  initial begin\n"
                       "    r = f(); rq = g(); get(oo);\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", r[0], r[1], "
                       "rq.size(), rq[1],\n"
                       "             oo[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 4 3 4 8\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnpackedArrayConcatSim, DISABLED_InputArgumentsTakeTheConcatenation) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a = 3, b = 4;\n"
                       "  function int f1(input int x[2]);\n"
                       "    return x[0] * 10 + x[1];\n"
                       "  endfunction\n"
                       "  function int f2(input int q[$]);\n"
                       "    return q.size() * 100 + q[1];\n"
                       "  endfunction\n"
                       "  function int f3(input int d[]);\n"
                       "    return d.size() * 100 + d[1];\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d %0d %0d\", f1({a, b}), "
                       "f2({a, b, a}),\n"
                       "                   f3({b, a}));\n"
                       "endmodule\n",
                       f),
            "34 304 203\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnpackedArrayConcatSim, DISABLED_InputPortTakesTheConcatenation) {
  for (const char* declaration :
       {"module s(input var int x[2]);\n"
        "  initial #1 $display(\"%0d %0d\", x[0], x[1]);\n"
        "endmodule\n",
        "interface s(input var int x[2]);\n"
        "  initial #1 $display(\"%0d %0d\", x[0], x[1]);\n"
        "endinterface\n",
        "program s(input var int x[2]);\n"
        "  initial #1 $display(\"%0d %0d\", x[0], x[1]);\n"
        "endprogram\n"}) {
    const std::string kSrc = std::string(declaration) +
                             "module t;\n"
                             "  int a = 5, b = 6;\n"
                             "  s u(.x({a, b}));\n"
                             "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(kSrc, f), "5 6\n") << kSrc;
    EXPECT_FALSE(f.diag.HasErrors()) << kSrc;
  }
}

TEST(UnpackedArrayConcatSim,
     DISABLED_ParameterValueAndOverrideTakeTheConcatenation) {
  for (const auto& [instance, expected] :
       {std::pair{"  m u();\n", "1 2\n"},
        std::pair{"  m #(.P({3, 4})) u();\n", "3 4\n"}}) {
    const std::string kSrc =
        std::string(
            "module m #(parameter int P[2] = {1, 2});\n"
            "  initial $display(\"%0d %0d\", P[0], P[1]);\n"
            "endmodule\n"
            "module t;\n") +
        instance + "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(kSrc, f), expected) << kSrc;
    EXPECT_FALSE(f.diag.HasErrors()) << kSrc;
  }
}

TEST(UnpackedArrayConcatSim, ConcatenationInAPackageClassInterfaceAndProgram) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  function automatic int f();\n"
                 "    int q[$]; q = {1, 2, 3}; return q.size();\n"
                 "  endfunction\n"
                 "endpackage\n"
                 "class C;\n"
                 "  int q[$];\n"
                 "  function int g(); q = {4, 5}; q = {q, q}; return q.size(); "
                 "endfunction\n"
                 "endclass\n"
                 "interface I;\n"
                 "  int a[2];\n"
                 "  initial begin a = {7, 8}; $display(\"I %0d\", a[1]); end\n"
                 "endinterface\n"
                 "program P;\n"
                 "  int d[];\n"
                 "  initial begin d = {1, 2, 3, 4}; #1 $display(\"P %0d\", "
                 "d.size()); end\n"
                 "endprogram\n"
                 "module t;\n"
                 "  I i(); P pp(); C c;\n"
                 "  initial begin c = new; $display(\"%0d %0d\", p::f(), "
                 "c.g()); end\n"
                 "endmodule\n",
                 f),
      "3 4\nI 8\nP 4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
