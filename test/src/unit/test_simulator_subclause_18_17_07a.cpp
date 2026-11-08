#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_string_var.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RandseqValuePassingSim, ArgumentAvailableThroughoutProduction) {
  SimFixture f;
  auto [a, b] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int a;\n"
                       "  int b;\n"
                       "  initial begin\n"
                       "    a = 0; b = 0;\n"
                       "    randsequence(main)\n"
                       "      main : compute(9) ;\n"
                       "      compute( int v ) : { a = v; } { b = v + 1; } ;\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "a", "b");
  EXPECT_EQ(a, 9u);
  EXPECT_EQ(b, 10u);
}

TEST(RandseqValuePassingSim, DefaultArgumentUsedWhenOmitted) {
  SimFixture f;
  uint64_t got = RunModule(f,
                           "module t;\n"
                           "  int got;\n"
                           "  initial begin\n"
                           "    got = 0;\n"
                           "    randsequence(main)\n"
                           "      main : compute ;\n"
                           "      compute( int v = 9 ) : { got = v; } ;\n"
                           "    endsequence\n"
                           "  end\n"
                           "endmodule\n",
                           "got");
  EXPECT_EQ(got, 9u);
}

TEST(RandseqValuePassingSim, ReturnValueReadByTriggeringProduction) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : a { r = a; } ;\n"
                         "      int a : { return 7; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 7u);
}

TEST(RandseqValuePassingSim, MultipleAppearancesIndexedInSyntacticOrder) {
  SimFixture f;
  auto [r1, r2] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int n;\n"
                       "  int r1;\n"
                       "  int r2;\n"
                       "  initial begin\n"
                       "    n = 0; r1 = 0; r2 = 0;\n"
                       "    randsequence(main)\n"
                       "      void main : a a { r1 = a[1]; r2 = a[2]; } ;\n"
                       "      int a : { n = n + 1; return n; } ;\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "r1", "r2");
  EXPECT_EQ(r1, 1u);
  EXPECT_EQ(r2, 2u);
}

TEST(RandseqValuePassingSim, NoReturnTypeProductionYieldsNoValue) {
  SimFixture f;
  uint64_t captured = RunModule(f,
                                "module t;\n"
                                "  int x;\n"
                                "  int captured;\n"
                                "  initial begin\n"
                                "    x = 88;\n"
                                "    captured = 0;\n"
                                "    randsequence(main)\n"
                                "      void main : x { captured = x; } ;\n"
                                "      x : { } ;\n"
                                "    endsequence\n"
                                "  end\n"
                                "endmodule\n",
                                "captured");
  EXPECT_EQ(captured, 88u);
}

TEST(RandseqValuePassingSim, ArgumentInThenValueOut) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : mk(10) { r = mk; } ;\n"
                         "      int mk( int base ) : { return base + 5; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 15u);
}

TEST(RandseqValuePassingSim, OnlyAlreadyGeneratedValuesAreAvailable) {
  SimFixture f;
  auto [pre, after] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int a;\n"
                       "  int pre;\n"
                       "  int after;\n"
                       "  initial begin\n"
                       "    a = 99; pre = 0; after = 0;\n"
                       "    randsequence(main)\n"
                       "      void main : { pre = a; } a { after = a; } ;\n"
                       "      int a : { return 7; } ;\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "pre", "after");
  EXPECT_EQ(pre, 99u);
  EXPECT_EQ(after, 7u);
}

TEST(RandseqValuePassingSim, MultipleArgumentsBoundByPosition) {
  SimFixture f;
  uint64_t got =
      RunModule(f,
                "module t;\n"
                "  int got;\n"
                "  initial begin\n"
                "    got = 0;\n"
                "    randsequence(main)\n"
                "      main : combine(3, 4) ;\n"
                "      combine( int a, int b ) : { got = a * 10 + b; } ;\n"
                "    endsequence\n"
                "  end\n"
                "endmodule\n",
                "got");
  EXPECT_EQ(got, 34u);
}

TEST(RandseqValuePassingSim, ArgumentPassedThroughConditionalProduction) {
  SimFixture f;
  uint64_t got = RunModule(f,
                           "module t;\n"
                           "  int got;\n"
                           "  int sel;\n"
                           "  initial begin\n"
                           "    got = 0; sel = 1;\n"
                           "    randsequence(main)\n"
                           "      void main : pick ;\n"
                           "      pick : if (sel) hi(7) else lo(9) ;\n"
                           "      hi( int v ) : { got = v; } ;\n"
                           "      lo( int v ) : { got = v; } ;\n"
                           "    endsequence\n"
                           "  end\n"
                           "endmodule\n",
                           "got");
  EXPECT_EQ(got, 7u);
}

TEST(RandseqValuePassingSim, SeparateCallsBindOwnArguments) {
  SimFixture f;
  uint64_t sum = RunModule(f,
                           "module t;\n"
                           "  int sum;\n"
                           "  initial begin\n"
                           "    sum = 0;\n"
                           "    randsequence(main)\n"
                           "      void main : add(3) add(5) ;\n"
                           "      add( int v ) : { sum = sum + v; } ;\n"
                           "    endsequence\n"
                           "  end\n"
                           "endmodule\n",
                           "sum");
  EXPECT_EQ(sum, 8u);
}

TEST(RandseqValuePassingSim, OmittedTrailingArgumentUsesDefault) {
  SimFixture f;
  uint64_t got =
      RunModule(f,
                "module t;\n"
                "  int got;\n"
                "  initial begin\n"
                "    got = 0;\n"
                "    randsequence(main)\n"
                "      main : combine(3) ;\n"
                "      combine( int a, int b = 5 ) : { got = a * 10 + b; } ;\n"
                "    endsequence\n"
                "  end\n"
                "endmodule\n",
                "got");
  EXPECT_EQ(got, 35u);
}

TEST(RandseqValuePassingSim, NestedProductionReturnValues) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : outer { r = outer; } ;\n"
                         "      int outer : inner { return inner; } ;\n"
                         "      int inner : { return 3; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 3u);
}

TEST(RandseqValuePassingSim, IfBranchProductionWritesTheFirstImplicitElement) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int cond;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    cond = 1;\n"
                         "    randsequence(main)\n"
                         "      void main : if (cond) mk(5) else mk(20)\n"
                         "                  { r = mk[1]; } ;\n"
                         "      int mk (int v) : { return v; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 5u);
}

TEST(RandseqValuePassingSim,
     ElseBranchProductionWritesTheSecondImplicitElement) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int cond;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    cond = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : if (cond) mk(5) else mk(20)\n"
                         "                  { r = mk[2]; } ;\n"
                         "      int mk (int v) : { return v; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 20u);
}

TEST(RandseqValuePassingSim,
     RepeatedProductionWritesOneScalarImplicitVariable) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int n;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    n = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : repeat(3) c { r = c; } ;\n"
                         "      int c : { n = n + 1; return n; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 3u);
}

TEST(RandseqValuePassingSim, CaseItemProductionWritesItsImplicitVariable) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int sel;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    sel = 2;\n"
                         "    randsequence(main)\n"
                         "      void main : case (sel) 1 : p1; 2 : p2;\n"
                         "                  endcase { r = p2; } ;\n"
                         "      int p1 : { return 3; } ;\n"
                         "      int p2 : { return 7; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 7u);
}

TEST(RandseqValuePassingSim,
     VoidProductionReturnLeavesTheTriggeringValueAlone) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 55;\n"
                         "    randsequence(main)\n"
                         "      void main : outer { r = outer + 1; } ;\n"
                         "      int outer : inner ;\n"
                         "      void inner : { return 9; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
}

TEST(RandseqValuePassingSim, StringReturnTypeProductionCarriesItsText) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  string r;\n"
      "  initial begin\n"
      "    r = \"unset\";\n"
      "    randsequence(main)\n"
      "      void main : op { r = op; $display(op); } ;\n"
      "      string op : { return \"+\"; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "+\n");
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "+");
}

TEST(RandseqValuePassingSim, StringReturnTypeArrayElementsCarryTheirText) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  string r1;\n"
      "  string r2;\n"
      "  initial begin\n"
      "    r1 = \"unset\"; r2 = \"unset\";\n"
      "    randsequence(main)\n"
      "      void main : op(1) op(2)\n"
      "                  { r1 = op[1]; r2 = op[2];\n"
      "                    $display(op[1]); $display(op[2]); } ;\n"
      "      string op ( int k ) :\n"
      "        { if (k == 1) return \"minus\"; return \"times\"; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "minus\ntimes\n");
  auto* first = f.ctx.FindVariable("r1");
  auto* second = f.ctx.FindVariable("r2");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(VecToStr(first->value), "minus");
  EXPECT_EQ(VecToStr(second->value), "times");
}

TEST(RandseqValuePassingSim, StringReturnLongerThanFourCharactersSurvives) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  string r;\n"
      "  int n;\n"
      "  initial begin\n"
      "    r = \"unset\"; n = 0;\n"
      "    randsequence(main)\n"
      "      void main : op { r = op; n = op.len(); $display(op); } ;\n"
      "      string op : { return \"plusminus\"; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "plusminus\n");
  auto* text = f.ctx.FindVariable("r");
  auto* len = f.ctx.FindVariable("n");
  ASSERT_NE(text, nullptr);
  ASSERT_NE(len, nullptr);
  EXPECT_EQ(VecToStr(text->value), "plusminus");
  EXPECT_EQ(len->value.ToUint64(), 9u);
}

TEST(RandseqValuePassingSim, ImplicitArrayShapeDoesNotOutliveTheStatement) {
  SimFixture f;
  auto [in_rule, after] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  logic [7:0] a;\n"
                       "  int n;\n"
                       "  int in_rule;\n"
                       "  int after;\n"
                       "  initial begin\n"
                       "    a = 8'b1010_1010;\n"
                       "    n = 0; in_rule = 0; after = 0;\n"
                       "    randsequence(main)\n"
                       "      void main : a a { in_rule = a[2]; } ;\n"
                       "      int a : { n = n + 1; return n; } ;\n"
                       "    endsequence\n"
                       "    after = a[1];\n"
                       "  end\n"
                       "endmodule\n",
                       "in_rule", "after");
  EXPECT_EQ(in_rule, 2u);
  EXPECT_EQ(after, 1u);
}

TEST(RandseqValuePassingSim,
     ImplicitArrayShapeDoesNotReachTheNextRandsequence) {
  SimFixture f;
  auto [total, sel] = RunModuleTwoVars(
      f,
      "module t;\n"
      "  int total;\n"
      "  int sel;\n"
      "  initial begin\n"
      "    total = 0; sel = 0;\n"
      "    randsequence(main)\n"
      "      void main : p(20) p(30) { total = p[1] + p[2]; } ;\n"
      "      int p ( int k ) : { return k; } ;\n"
      "    endsequence\n"
      "    randsequence(main)\n"
      "      void main : p(6) { sel = p[1]; } ;\n"
      "      int p ( int k ) : { return k; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      "total", "sel");
  EXPECT_EQ(total, 50u);
  EXPECT_EQ(sel, 1u);
}

TEST(RandseqValuePassingSim, RecursiveActivationLeavesTheOuterArrayShape) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  int total;\n"
      "  initial begin\n"
      "    total = 0;\n"
      "    randsequence(main)\n"
      "      void main : p(1) p(2)\n"
      "                  { total = p[1] + p[2]; $display(\"%p\", p); } ;\n"
      "      int p ( int d ) : if (d) p(0) if (d) p(0) if (d) p(0)\n"
      "                        { return d + 40; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "'{41, 42}\n");
  auto* sum = f.ctx.FindVariable("total");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 83u);
}

TEST(RandseqValuePassingSim, TypedefNameReturnTypeValueReachesTheRule) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef byte octet;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : v { r = v; } ;\n"
                         "      octet v : { return 41; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 41u);
}

void RunRandJoinCapture(SimFixture& f, std::string_view main_rules,
                        uint64_t& r1, uint64_t& r2) {
  std::string src =
      "module t;\n"
      "  int p, q, r1, r2;\n"
      "  initial begin\n"
      "    p = 7; q = 8; r1 = 0; r2 = 0;\n"
      "    randsequence(main)\n"
      "      void main : " +
      std::string(main_rules) +
      ";\n"
      "      int p : { return 5; };\n"
      "      int q : { return 6; };\n"
      "      void alt : { r1 = 1; r2 = 2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n";
  auto [got1, got2] = RunModuleTwoVars(f, src.c_str(), "r1", "r2");
  r1 = got1;
  r2 = got2;
}

TEST(RandseqValuePassingSim, RandJoinOperandReturnValuesReachTheRuleCodeBlock) {
  SimFixture f;
  uint64_t r1 = 0;
  uint64_t r2 = 0;
  RunRandJoinCapture(f, "rand join p q := 1 { r1 = p; r2 = q; }", r1, r2);
  EXPECT_EQ(r1, 5u);
  EXPECT_EQ(r2, 6u);
}

TEST(RandseqValuePassingSim,
     RandJoinRuleSelectedByWeightReadsItsOperandValues) {
  SimFixture f;
  uint64_t r1 = 0;
  uint64_t r2 = 0;
  RunRandJoinCapture(f, "rand join p q := 5 { r1 = p; r2 = q; } | alt := 0", r1,
                     r2);
  EXPECT_EQ(r1, 5u);
  EXPECT_EQ(r2, 6u);
}

TEST(RandseqValuePassingSim, RandJoinOperandRuleReadsItsOwnProductionValue) {
  SimFixture f;
  auto [r1, r2] = RunModuleTwoVars(f,
                                   "module t;\n"
                                   "  int r1, r2;\n"
                                   "  initial begin\n"
                                   "    r1 = 0; r2 = 0;\n"
                                   "    randsequence(main)\n"
                                   "      void main : rand join a b;\n"
                                   "      void a : p := 1 { r1 = p; };\n"
                                   "      void b : q := 1 { r2 = q; };\n"
                                   "      int p : { return 5; };\n"
                                   "      int q : { return 6; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "r1", "r2");
  EXPECT_EQ(r1, 5u);
  EXPECT_EQ(r2, 6u);
}

TEST(RandseqValuePassingSim, RandJoinOperandBindsItsActualArguments) {
  SimFixture f;
  auto [r1, r2] = RunModuleTwoVars(
      f,
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = 0; r2 = 0;\n"
      "    randsequence(main)\n"
      "      void main : rand join D(5) D(20) := 1 { r1 = D[1]; r2 = D[2]; };\n"
      "      int D(int prm) : { return prm; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      "r1", "r2");
  EXPECT_EQ(r1, 5u);
  EXPECT_EQ(r2, 20u);
}

TEST(RandseqValuePassingSim, TwoRandJoinOperandsOfOneProductionDoNotAlias) {
  SimFixture f;
  auto [r1, r2] = RunModuleTwoVars(f,
                                   "module t;\n"
                                   "  int r1, r2, n;\n"
                                   "  initial begin\n"
                                   "    r1 = 0; r2 = 0; n = 0;\n"
                                   "    randsequence(main)\n"
                                   "      void main : rand join w(1) w(2);\n"
                                   "      void w(int k) : v := 1 "
                                   "{ if (k == 1) r1 = v; else r2 = v; };\n"
                                   "      int v : { n = n + 1; return n; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "r1", "r2");
  EXPECT_EQ(r1 + r2, 3u);
  EXPECT_NE(r1, r2);
}

TEST(RandseqValuePassingSim, RandJoinOperandReturnWritesItsOwnValue) {
  SimFixture f;
  auto [r1, r2] = RunModuleTwoVars(
      f,
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = 0; r2 = 0;\n"
      "    randsequence(main)\n"
      "      void main : top := 1 { r1 = top; };\n"
      "      int top : rand join a b := 1 { r2 = a; return 7; };\n"
      "      int a : p := 1 { return 41; };\n"
      "      void b : p;\n"
      "      void p : { };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      "r1", "r2");
  EXPECT_EQ(r1, 7u);
  EXPECT_EQ(r2, 41u);
}

}  // namespace
