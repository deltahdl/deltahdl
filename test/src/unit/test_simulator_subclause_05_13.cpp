#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BuiltinMethodSim, ArraySizeWithParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [];\n"
      "  logic [31:0] s;\n"
      "  initial begin arr = new[4]; s = arr.size(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 4u);
}

TEST(BuiltinMethodSim, ArraySizeNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [];\n"
      "  logic [31:0] s;\n"
      "  initial begin arr = new[3]; s = arr.size; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

TEST(BuiltinMethodSim, MethodInExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [];\n"
      "  logic [31:0] r;\n"
      "  initial begin arr = new[5]; r = arr.size() + 32'd1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 6u);
}

TEST(BuiltinMethodSim, QueuePushBackAndSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    q.push_back(8'hBB);\n"
      "    s = q.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

TEST(BuiltinMethodSim, QueuePushBackElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h42);\n"
      "    q.push_back(8'h43);\n"
      "    q.push_back(8'h44);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x42u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x43u);
  EXPECT_EQ(q->elements[2].ToUint64(), 0x44u);
}

TEST(BuiltinMethodSim, QueuePopFront) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'h10);\n"
      "    q.push_back(8'h20);\n"
      "    q.push_back(8'h30);\n"
      "    q.pop_front();\n"
      "    s = q.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x30u);
}

TEST(BuiltinMethodSim, DynArraySize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] dyn [] = '{8'hDE, 8'hAD};\n"
      "  logic [31:0] s;\n"
      "  initial s = dyn.size();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

TEST(BuiltinMethodSim, StringLen) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s = \"hello\";\n"
      "  logic [31:0] n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 5u);
}

TEST(BuiltinMethodSim, DynArraySizeNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] dyn [] = '{8'h11, 8'h22, 8'h33};\n"
      "  logic [31:0] s;\n"
      "  initial s = dyn.size;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

TEST(BuiltinMethodSim, StringLenNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s = \"world\";\n"
      "  logic [31:0] n;\n"
      "  initial n = s.len;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 5u);
}

TEST(BuiltinMethodSim, EnumNum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "  logic [31:0] n;\n"
      "  initial n = c.num();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 3u);
}

TEST(BuiltinMethodSim, MethodNoParensInBinaryExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [];\n"
      "  logic [31:0] r;\n"
      "  initial begin arr = new[5]; r = arr.size + 32'd1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 6u);
}

TEST(BuiltinMethodSim, EnumNextNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum logic [1:0] {RED, GREEN, BLUE} color_e;\n"
      "  color_e c = RED;\n"
      "  logic [1:0] n;\n"
      "  initial n = c.next;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 1u);
}

TEST(BuiltinMethodSim, EnumPrevNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum logic [1:0] {RED, GREEN, BLUE} color_e;\n"
      "  color_e c = BLUE;\n"
      "  logic [1:0] n;\n"
      "  initial n = c.prev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 1u);
}

TEST(BuiltinMethodSim, MethodResultInConditional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] r;\n"
      "  initial begin\n"
      "    q.push_back(8'hFF);\n"
      "    if (q.size() > 0)\n"
      "      r = 32'd1;\n"
      "    else\n"
      "      r = 32'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 1u);
}

TEST(BuiltinMethodSim, ImplicitVariableWithParenthesesIsTheResult) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  string s = \"ab\";\n"
      "  initial $display(\"%0d %0d %0d\", q.min()[0], s.toupper()[1],\n"
      "                   q.unique().size());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 66 3\n");
}

TEST(BuiltinMethodSim, ImplicitVariableOfAnUnnamedValuesMethodIsTheResult) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  string s = \"abcde\";\n"
      "  initial $display(\"%0d %0d %0d\", $sformatf(\"%0d\", "
      "12345).len()[2],\n"
      "                   (s).len()[1], (q).min()[0]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1\n");
}

TEST(BuiltinMethodSim, LastCallOfAChainWithoutParenthesesIsCalled) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  initial $display(\"%0d\", q.unique().size);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3\n");
}

TEST(BuiltinMethodSim, LastBareCallOnEachReceiversResultIsCalled) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  int d[] = '{5, 5, 6};\n"
      "  int fx[4] = '{7, 7, 7, 8};\n"
      "  int aa[string] = '{\"a\": 1, \"b\": 1};\n"
      "  string s = \"aB\";\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d %0d\", q.unique().size, d.unique().size,\n"
      "             fx.unique().size, aa.unique().size);\n"
      "    $display(\"%0d %0d\", q.find() with (item > 1).size,\n"
      "             q.unique_index().size);\n"
      "    $display(\"%0d %0d %0d\", q.unique().sum, q.unique().product,\n"
      "             q.unique().unique().size);\n"
      "    $display(\"%0d %s %s\", s.toupper().len, s.toupper().tolower,\n"
      "             s.tolower().toupper);\n"
      "    $display(\"%0d\", q.unique().sum with (item * 2));\n"
      "    $display(\"%0d\", q.unique().unique().size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 2 2 1\n2 3\n6 6 3\n2 ab AB\n12\n3\n");
}

TEST(BuiltinMethodSim, LastBareCallOnAFunctionsResultIsCalledOnce) {
  SimFixture f;
  auto out = RunCapture(
      "typedef int iq_t[$];\n"
      "class C;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  int calls = 0;\n"
      "  function iq_t getq(); calls++; return q; endfunction\n"
      "  function string gets(); calls++; return \"xyz\"; endfunction\n"
      "  function C me(); calls++; return this; endfunction\n"
      "  function int inside_(); return getq().size; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C o = new;\n"
      "  int calls = 0;\n"
      "  function automatic string fs(); calls++; return \"abcd\"; "
      "endfunction\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", fs().len, calls);\n"
      "    $display(\"%0d %0d\", o.getq().size, o.calls);\n"
      "    $display(\"%0d %0d\", o.gets().len, o.calls);\n"
      "    $display(\"%0d %0d\", o.me().getq().size, o.calls);\n"
      "    $display(\"%0d %0d\", o.me().q.size, o.calls);\n"
      "    $display(\"%0d %0d\", o.inside_(), o.calls);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 1\n4 1\n3 2\n4 4\n4 5\n4 6\n");
}

TEST(BuiltinMethodSim, MemberOfACallsResultNamedAsAMethodIsRead) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  typedef struct {int size; int len; int sum;} st_t;\n"
      "  class C;\n"
      "    int size = 5;\n"
      "    int num = 6;\n"
      "  endclass\n"
      "  C c = new;\n"
      "  int calls = 0;\n"
      "  function automatic st_t fst();\n"
      "    st_t r;\n"
      "    calls++;\n"
      "    r.size = 7; r.len = 8; r.sum = 9;\n"
      "    return r;\n"
      "  endfunction\n"
      "  function automatic C fc(); calls++; return c; endfunction\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d\", fst().size, fst().len, fst().sum);\n"
      "    $display(\"%0d %0d %0d\", fc().size, fc().num, calls);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 8 9\n5 6 5\n");
}

}  // namespace
