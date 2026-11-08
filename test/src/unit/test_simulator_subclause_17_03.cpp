#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/checker_instance_scheduling.h"

using namespace delta;

namespace {

TEST(CheckerInstanceScheduling, ProceduralVersusStaticClassification) {
  EXPECT_EQ(ClassifyCheckerInstance(true), CheckerInstanceKind::kProcedural);
  EXPECT_EQ(ClassifyCheckerInstance(false), CheckerInstanceKind::kStatic);
}

TEST(CheckerInstanceScheduling, OnlyStaticAssertionsAreExemptFromEveryStep) {
  EXPECT_TRUE(CheckerContentExistsEveryTimeStep(false));
  EXPECT_FALSE(CheckerContentExistsEveryTimeStep(true));
}

TEST(CheckerInstanceScheduling, StaticConcurrentAssertionTreatment) {
  EXPECT_EQ(TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, StaticDeferredAssertionTreatment) {
  EXPECT_EQ(TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, NestedStaticCheckerFollowsTopLevelAncestor) {
  EXPECT_EQ(EffectiveKindForStaticAssertions(CheckerInstanceKind::kStatic, true,
                                             CheckerInstanceKind::kProcedural),
            CheckerInstanceKind::kProcedural);
  EXPECT_EQ(EffectiveKindForStaticAssertions(CheckerInstanceKind::kStatic, true,
                                             CheckerInstanceKind::kStatic),
            CheckerInstanceKind::kStatic);
  EXPECT_EQ(
      EffectiveKindForStaticAssertions(CheckerInstanceKind::kStatic, false,
                                       CheckerInstanceKind::kProcedural),
      CheckerInstanceKind::kStatic);
  EXPECT_EQ(
      EffectiveKindForStaticAssertions(CheckerInstanceKind::kProcedural, false,
                                       CheckerInstanceKind::kStatic),
      CheckerInstanceKind::kProcedural);
}

TEST(CheckerInstanceScheduling, ACheckerDeclaredInAPackageIsInstantiated) {
  SimFixture f;
  auto* c_pass = RunAndFindVar(
      "package q;\n"
      "  parameter int unused = 0;\n"
      "endpackage\n"
      "package p;\n"
      "  checker chk(logic a, logic clk);\n"
      "    int pass = 0, fail = 0;\n"
      "    a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
      "  endchecker\n"
      "endpackage\n"
      "module top;\n"
      "  import q::unused;\n"
      "  import q::*;\n"
      "  import p::*;\n"
      "  logic clk = 0, a = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  p::chk c(a, clk);\n"
      "  chk c2(a, clk);\n"
      "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(c_pass, nullptr);
  EXPECT_EQ(c_pass->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c2.pass")->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c2.fail")->value.ToUint64(), 2u);
}

TEST(CheckerInstanceScheduling, AConstantFormalSelectsAGenerateBlock) {
  SimFixture f;
  auto* c_cov = RunAndFindVar(
      "typedef enum { cover_none, cover_all } coverage_level;\n"
      "checker chk(logic clk, int lvl, coverage_level clevel = cover_all);\n"
      "  int cov = 0;\n"
      "  if (lvl != 0 && clevel != cover_none) begin : cover_b\n"
      "    c1: cover property (@(posedge clk) 1) cov++;\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk, 1);\n"
      "  chk d(.clk(clk), .lvl(0));\n"
      "  chk e(clk, 2, cover_none);\n"
      "  initial #7 $finish;\n"
      "endmodule\n",
      f, "c.cov");
  ASSERT_NE(c_cov, nullptr);
  EXPECT_EQ(c_cov->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("d.cov")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("e.cov")->value.ToUint64(), 0u);
}

TEST(CheckerInstanceScheduling, AStringFormalCarriesItsActualOrDefault) {
  SimFixture f;
  auto* len = RunAndFindVar(
      "checker chk(logic clk, string msg = \"violation-long\");\n"
      "  int len = 0, same = 0;\n"
      "  a1: assert property (@(posedge clk) 0) else begin\n"
      "    len = msg.len();\n"
      "    same = msg == \"violation-long\" || msg == \"boom\";\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  chk c2(clk, \"boom\");\n"
      "  initial #12 $finish;\n"
      "endmodule\n",
      f, "c.len");
  ASSERT_NE(len, nullptr);
  EXPECT_EQ(len->value.ToUint64(), 14u);
  EXPECT_EQ(f.ctx.FindVariable("c.same")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("c2.len")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2.same")->value.ToUint64(), 1u);
}

TEST(CheckerInstanceScheduling, AnEventFormalClocksTheCheckersAssertion) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(logic a, event clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@clk a) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  event ev;\n"
      "  always #5 begin clk = ~clk; -> ev; end\n"
      "  chk c(a, ev);\n"
      "  chk c2(a, clk);\n"
      "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2.pass")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("c2.fail")->value.ToUint64(), 4u);
}

TEST(CheckerInstanceScheduling, AFormalBoundsACycleDelay) {
  SimFixture f;
  auto* p1 = RunAndFindVar(
      "checker chk(logic a, b, int n, untyped m, logic clk);\n"
      "  int p1 = 0, p2 = 0, p3 = 0, p4 = 0;\n"
      "  a1: assert property (@(posedge clk) a |-> ##n b) p1++;\n"
      "  a2: assert property (@(posedge clk) a |-> ##[1:m] b) p2++;\n"
      "  a3: assert property (@(posedge clk) a |-> (##n b or ##[1:m] b))\n"
      "    p3++;\n"
      "  a4: assert property (@(posedge clk)\n"
      "    a |-> 1'b1 ##0 (##n b or 1'b0)) p4++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 0, b = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(a, b, 2, $, clk);\n"
      "  initial begin #2 a = 1; #10 a = 0; #10 b = 1; #30 $finish; end\n"
      "endmodule\n",
      f, "c.p1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(p1->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.p2")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.p3")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.p4")->value.ToUint64(), 5u);
}

TEST(CheckerInstanceScheduling, AnEdgeActualClocksTheCheckersAssertion) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(logic a, event clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@clk a) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(a, posedge clk);\n"
      "  chk c2(.a(a), .clk(negedge clk));\n"
      "  initial begin #17 a = 0; #5 a = 1; #30 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c2.pass")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2.fail")->value.ToUint64(), 1u);
}

TEST(CheckerInstanceScheduling, ASequenceActualStandsForItsFormal) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(sequence s, logic b, logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) s |-> b) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1, b = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(a ##1 a, b, clk);\n"
      "  initial begin #32 b = 0; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 2u);
}

TEST(CheckerInstanceScheduling, APropertyActualStandsForItsFormal) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(property p, logic a, logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) p) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1, b = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(a |-> b, !a, clk);\n"
      "  initial begin #32 b = 0; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 2u);
}

TEST(CheckerInstanceScheduling, ASequenceActualReadsSampledValues) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(sequence s, logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) s) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, y = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  always @(posedge clk) y <= ~y;\n"
      "  chk c(y ##0 1, clk);\n"
      "  initial #52 $finish;\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 2u);
}

TEST(CheckerInstanceScheduling, APropertyActualReadsItsOwnInstance) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(property p, logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) p) pass++; else fail++;\n"
      "endchecker\n"
      "module m(input logic clk, input logic b);\n"
      "  logic a = 1;\n"
      "  chk c(a |-> $countones({a, b}) == 2, clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  m u1(clk, 1'b1);\n"
      "  m u2(clk, 1'b0);\n"
      "  initial #52 $finish;\n"
      "endmodule\n",
      f, "u1.c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("u2.c.pass")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("u2.c.fail")->value.ToUint64(), 5u);
}

constexpr const char* kCountingChecker =
    "checker chk(logic a, logic clk);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
    "endchecker\n";

std::pair<uint64_t, uint64_t> CountsOver(const std::string& checker,
                                         const std::string& module,
                                         const std::string& scope) {
  SimFixture f;
  auto* pass = RunAndFindVar(checker + module, f, scope + ".pass");
  if (pass == nullptr) return {~0ull, ~0ull};
  return {pass->value.ToUint64(),
          f.ctx.FindVariable(scope + ".fail")->value.ToUint64()};
}

std::pair<uint64_t, uint64_t> CheckerCounts(const std::string& module,
                                            const std::string& scope) {
  return CountsOver(kCountingChecker, module, scope);
}

TEST(ProceduralCheckerInstance, ItsAssertionIsQueuedWhenTheStatementIsReached) {
  EXPECT_EQ(CheckerCounts("module top;\n"
                          "  logic clk = 0, a = 1, en = 1;\n"
                          "  always #5 clk = ~clk;\n"
                          "  always @(posedge clk) begin\n"
                          "    if (en) chk c(a, clk);\n"
                          "  end\n"
                          "  initial begin #12 a = 0; #10 en = 0; #10 a = 1; "
                          "#10 en = 1; #10 $finish; end\n"
                          "endmodule\n",
                          "c"),
            std::make_pair(2ull, 1ull));
}

TEST(ProceduralCheckerInstance, ReachedOnceItIsEvaluatedOnce) {
  EXPECT_EQ(CheckerCounts("module top;\n"
                          "  logic clk = 0, a = 1;\n"
                          "  always #5 clk = ~clk;\n"
                          "  initial begin\n"
                          "    @(posedge clk);\n"
                          "    chk c(a, clk);\n"
                          "  end\n"
                          "  initial begin #12 a = 0; #20 a = 1; #20 $finish; "
                          "end\n"
                          "endmodule\n",
                          "c"),
            std::make_pair(1ull, 0ull));
}

TEST(ProceduralCheckerInstance, EachInstanceKeepsItsOwnAssertion) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      std::string(kCountingChecker) +
          "module top;\n"
          "  logic clk = 0, a = 1, b = 1, en = 1;\n"
          "  always #5 clk = ~clk;\n"
          "  chk s(a, clk);\n"
          "  always @(posedge clk) begin\n"
          "    if (en) begin chk p1(a, clk); chk p2(b, clk); end\n"
          "  end\n"
          "  initial begin #12 a = 0; #10 en = 0; #10 a = 1; en = 1; b = 0;\n"
          "    #20 $finish; end\n"
          "endmodule\n",
      f, "s.pass");
  ASSERT_NE(pass, nullptr);
  auto value = [&f](const char* name) {
    return f.ctx.FindVariable(name)->value.ToUint64();
  };
  EXPECT_EQ(value("s.pass"), 3u);
  EXPECT_EQ(value("s.fail"), 2u);
  EXPECT_EQ(value("p1.pass"), 3u);
  EXPECT_EQ(value("p1.fail"), 1u);
  EXPECT_EQ(value("p2.pass"), 2u);
  EXPECT_EQ(value("p2.fail"), 2u);
}

TEST(ProceduralCheckerInstance, ItsOtherContentsRunAtEveryStep) {
  SimFixture f;
  auto* sum = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  int sum = 0, pass = 0, fail = 0;\n"
      "  always_ff @(posedge clk) sum <= sum + 1;\n"
      "  p1: assert property (@(posedge clk) sum < 3) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, en = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  always @(posedge clk) begin\n"
      "    if (en) chk c(clk);\n"
      "  end\n"
      "  initial begin #22 en = 0; #20 en = 1; #10 $finish; end\n"
      "endmodule\n",
      f, "c.sum");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.pass")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 1u);
}

TEST(ProceduralCheckerInstance, ItsDeferredAssertionIsReportedWhenReached) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(logic a, b);\n"
      "  int pass = 0, fail = 0;\n"
      "  function void inc_pass(); pass++; endfunction\n"
      "  function void inc_fail(); fail++; endfunction\n"
      "  a1: assert #0 (a != b) inc_pass(); else inc_fail();\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1, b = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always @(posedge clk) begin\n"
      "    chk c(a, b);\n"
      "  end\n"
      "  initial begin #10 a = 0; #10 b = 1; #10 a = 1; #10 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 2u);
}

TEST(ProceduralCheckerInstance, AnInterfacesProcedureInstantiatesOne) {
  EXPECT_EQ(CheckerCounts("interface ifc(input logic clk);\n"
                          "  logic a = 1;\n"
                          "  always @(posedge clk) begin\n"
                          "    chk k(a, clk);\n"
                          "  end\n"
                          "endinterface\n"
                          "module top;\n"
                          "  logic clk = 0;\n"
                          "  always #5 clk = ~clk;\n"
                          "  ifc i(clk);\n"
                          "  initial begin #12 i.a = 0; #20 i.a = 1; #20 "
                          "$finish; end\n"
                          "endmodule\n",
                          "i.k"),
            std::make_pair(3ull, 2ull));
}

TEST(ProceduralCheckerInstance, ANestedStaticInstanceFollowsItsAncestor) {
  EXPECT_EQ(CheckerCounts("checker outer(logic a, logic clk);\n"
                          "  chk i(a, clk);\n"
                          "endchecker\n"
                          "module top;\n"
                          "  logic clk = 0, a = 1, en = 1;\n"
                          "  always #5 clk = ~clk;\n"
                          "  always @(posedge clk) begin\n"
                          "    if (en) outer o(a, clk);\n"
                          "  end\n"
                          "  initial begin #12 a = 0; #10 en = 0; #10 a = 1; "
                          "#10 en = 1; #10 $finish; end\n"
                          "endmodule\n",
                          "o.i"),
            std::make_pair(2ull, 1ull));
}

TEST(ProceduralCheckerInstance, APackageCheckerIsInstantiatedInAProcedure) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "package p;\n"
      "  checker chk(logic a, logic clk);\n"
      "    int pass = 0, fail = 0;\n"
      "    a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
      "  endchecker\n"
      "endpackage\n"
      "module top;\n"
      "  logic clk = 0, a = 1, en = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  always @(posedge clk) begin\n"
      "    if (en) p::chk c(a, clk);\n"
      "  end\n"
      "  initial begin #12 a = 0; #10 en = 0; #10 a = 1; #10 en = 1; "
      "#10 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 1u);
}

TEST(ProceduralCheckerInstance, AnAutomaticInTheActualIsSavedWhenQueued) {
  EXPECT_EQ(CheckerCounts("module top;\n"
                          "  logic clk = 0;\n"
                          "  logic arr [20:0];\n"
                          "  always #5 clk = ~clk;\n"
                          "  initial begin\n"
                          "    for (int i = 0; i < 21; i++) arr[i] = 0;\n"
                          "    arr[5] = 1; arr[20] = 1;\n"
                          "  end\n"
                          "  always @(posedge clk) begin\n"
                          "    automatic int v1 = 0;\n"
                          "    for (int i = 0; i < 4; i++) begin\n"
                          "      v1 = v1 + 5;\n"
                          "      if (i != 2) chk c(arr[v1], clk);\n"
                          "    end\n"
                          "  end\n"
                          "  initial #52 $finish;\n"
                          "endmodule\n",
                          "c"),
            std::make_pair(10ull, 5ull));
}

TEST(ProceduralCheckerInstance, AStaticBesideTheSavedAutomaticIsSampled) {
  EXPECT_EQ(CheckerCounts("module top;\n"
                          "  logic clk = 0, b = 1;\n"
                          "  always #5 clk = ~clk;\n"
                          "  always @(posedge clk) begin\n"
                          "    automatic int k = 1;\n"
                          "    b = ~b;\n"
                          "    chk c(b && k == 1, clk);\n"
                          "  end\n"
                          "  initial #52 $finish;\n"
                          "endmodule\n",
                          "c"),
            std::make_pair(3ull, 2ull));
}

std::string ReachedWithAnAutomatic(const std::string& inst) {
  return "module top;\n"
         "  logic clk = 0;\n"
         "  int n = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) begin\n"
         "    automatic int k = n;\n"
         "    n <= n + 1;\n"
         "    " +
         inst +
         "\n"
         "  end\n"
         "  initial #52 $finish;\n"
         "endmodule\n";
}

TEST(ProceduralCheckerInstance, ASequenceReadsTheSavedActualAtEachTick) {
  EXPECT_EQ(CountsOver("checker chk(logic a, logic clk);\n"
                       "  int pass = 0, fail = 0;\n"
                       "  a1: assert property (@(posedge clk) a ##1 a)\n"
                       "    pass++; else fail++;\n"
                       "endchecker\n",
                       ReachedWithAnAutomatic("chk c(k[0], clk);"), "c"),
            std::make_pair(2ull, 3ull));
}

TEST(ProceduralCheckerInstance, EachOperandOfAnOrReadsTheSavedActual) {
  EXPECT_EQ(CountsOver("checker chk(logic a, logic clk);\n"
                       "  int pass = 0, fail = 0;\n"
                       "  a1: assert property (@(posedge clk) (a ##1 a) or a)\n"
                       "    pass++; else fail++;\n"
                       "endchecker\n",
                       ReachedWithAnAutomatic("chk c(k[0], clk);"), "c"),
            std::make_pair(2ull, 3ull));
}

TEST(ProceduralCheckerInstance, AnEventActualBesideTheSavedOneClocksIt) {
  EXPECT_EQ(
      CountsOver("checker chk(logic a, event ev);\n"
                 "  int pass = 0, fail = 0;\n"
                 "  a1: assert property (@ev a) pass++; else fail++;\n"
                 "endchecker\n",
                 ReachedWithAnAutomatic("chk c(k[0], posedge clk);"), "c"),
      std::make_pair(2ull, 3ull));
}

TEST(ProceduralCheckerInstance, AConstCastInTheActualIsSavedWhenQueued) {
  EXPECT_EQ(CheckerCounts("module top;\n"
                          "  logic clk = 0, b = 1;\n"
                          "  always #5 clk = ~clk;\n"
                          "  always @(posedge clk) begin\n"
                          "    b = ~b;\n"
                          "    chk c(const'(b), clk);\n"
                          "  end\n"
                          "  initial #52 $finish;\n"
                          "endmodule\n",
                          "c"),
            std::make_pair(2ull, 3ull));
}

TEST(CheckerInstanceScheduling, AnOutputIsAssignedInTheReactiveRegion) {
  SimFixture f;
  auto* saw = RunAndFindVar(
      "checker mutex(logic [1:0] sig, event clock, output bit failure);\n"
      "  assert property (@clock $onehot0(sig)) failure = 1'b0;\n"
      "    else failure = 1'b1;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  logic [1:0] bus = 2'b11;\n"
      "  logic res;\n"
      "  bit m_seen = 0;\n"
      "  mutex check_bus(bus, posedge clk, res);\n"
      "  always @(res) if (res) m_seen = 1;\n"
      "  checker obs;\n"
      "    bit saw = 1'b1;\n"
      "    always_ff @(posedge res) saw <= m_seen;\n"
      "  endchecker\n"
      "  obs o();\n"
      "  initial begin #1 clk = 1; #1 $finish; end\n"
      "endmodule\n",
      f, "o.saw");
  ASSERT_NE(saw, nullptr);
  EXPECT_EQ(f.ctx.FindVariable("res")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("m_seen")->value.ToUint64(), 1u);
  EXPECT_EQ(saw->value.ToUint64(), 0u);
}

TEST(CheckerInstanceScheduling, TriggeredOnASequenceFormalReadsItsActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "checker chk(sequence s, logic clk);\n"
      "  int hits = 0;\n"
      "  always_ff @(posedge clk) if (s.triggered) hits <= hits + 1;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1, b = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  sequence s_two; @(posedge clk) a ##1 a; endsequence\n"
      "  chk c1(s_two, clk);\n"
      "  chk c2(@(posedge clk) b, clk);\n"
      "  initial #52 $finish;\n"
      "endmodule\n",
      f, "c1.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2.hits")->value.ToUint64(), 5u);
}

}  // namespace
