#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/checker_instance_scheduling.h"

using namespace delta;

namespace {

TEST(CheckerInstanceScheduling, ProceduralVersusStaticClassification) {
  // §17.3: a checker instantiation in procedural code is a procedural checker
  // instance; one outside procedural code is a static checker instance.
  EXPECT_EQ(ClassifyCheckerInstance(/*instantiated_in_procedural_code=*/true),
            CheckerInstanceKind::kProcedural);
  EXPECT_EQ(ClassifyCheckerInstance(/*instantiated_in_procedural_code=*/false),
            CheckerInstanceKind::kStatic);
}

TEST(CheckerInstanceScheduling, OnlyStaticAssertionsAreExemptFromEveryStep) {
  // §17.3: all contents other than static assertion statements exist during
  // every time step; static assertion statements are the exception.
  EXPECT_TRUE(CheckerContentExistsEveryTimeStep(
      /*is_static_assertion_statement=*/false));
  EXPECT_FALSE(CheckerContentExistsEveryTimeStep(
      /*is_static_assertion_statement=*/true));
}

TEST(CheckerInstanceScheduling, StaticConcurrentAssertionTreatment) {
  // §17.3: a static concurrent assertion is monitored directly in a static
  // checker and queued (pending procedural assertion queue) in a procedural
  // checker.
  EXPECT_EQ(TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, StaticDeferredAssertionTreatment) {
  // §17.3: a static deferred assertion is monitored on expression change in a
  // static checker and queued (pending deferred assertion report) in a
  // procedural checker.
  EXPECT_EQ(TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, NestedStaticCheckerFollowsTopLevelAncestor) {
  // §17.3: a static checker statically instantiated inside another checker has
  // its static assertions follow the top-level ancestor's instance kind; an
  // un-nested checker keeps its own kind.
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/true,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kProcedural),
            CheckerInstanceKind::kProcedural);
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/true,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kStatic),
            CheckerInstanceKind::kStatic);
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/false,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kProcedural),
            CheckerInstanceKind::kStatic);
  // Edge: when not nested, the instance's own kind is returned regardless of
  // any ancestor kind, so a procedural own kind is preserved.
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kProcedural,
                /*nested_inside_another_checker=*/false,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kStatic),
            CheckerInstanceKind::kProcedural);
}

// §17.2 lets a checker be declared in a package, and §17.3's
// ps_checker_identifier instantiates it by the package's name, `p::chk`, or
// by a name an import made visible (§26.3), here past a package q whose
// wildcard import and explicit import of another name hold no checker. Each
// instance fails at 15 and 25 of the five posedges. Both were reported as
// unknown modules.
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

// §17.2 and §17.9: a checker formal whose actual, or default where the
// instance binds none, is an elaboration-time constant is that constant in
// the checker, so a conditional generate tests it (§27.5). c binds lvl to 1
// and takes clevel's default cover_all, keeping the cover; d binds lvl by
// name to 0 and e binds clevel to cover_none, dropping it. The condition was
// reported not constant and every instance dropped the block.
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

// §17.2 and §17.3: a checker formal of type string carries its actual, or
// its default where the instance binds none, into the checker body, an
// action block among it, whole: c takes the fourteen-character default and
// c2 the actual. The formal read as an empty string, having no width to be
// connected at, and a default was cut to its last eight characters.
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

// §17.2 and §17.3: an assertion clocked by a checker formal of type event
// waits on its actual, a named event c's module triggers at every clock edge
// and the clock signal itself for c2, so each is attempted at the ten edges
// from 5 to 50 and fails at the four where a is low. Neither was attempted:
// the formal, having no width, was never connected.
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

// §17.3: a checker formal written as a cycle delay's bound takes its
// actual, `##n` with n bound to 2 being `##2` and `##[1:m]` with m bound to
// `$` being `##[1:$]`, in an or's operands and in a group nested in a chain
// as well. a is high at the posedge at 5 alone and b from 25, so each
// assertion holds there, and vacuously at the other four posedges. Each
// bound was read as 1, failing at 15.
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

// §17.3: the actual of a checker's event formal is an event expression, so
// `@clk` in the checker waits on the edge the instance writes: c's posedge
// clk at 5, 15, 25, 35 and 45, and c2's negedge clk, bound by name, at 10 to
// 50. a is low from 17 to 22, over the negedge at 20 alone, so c holds at
// all five and c2 fails once. Both were parse errors.
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

// §17.2 and §17.3: the actual of a checker's sequence formal is a sequence
// expression, so `s |-> b` in the checker is `a ##1 a |-> b`. a is high
// throughout and b until 32, so the attempts from 5 and 15 end where b holds
// and those from 25 and 35 where it does not; the attempt from 45 is still
// open at 52. Read as `a` alone, the formal would pass three times. The
// actual was a parse error.
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

// §17.2 and §17.3: the actual of a checker's property formal is a property
// expression, so `assert property (@(posedge clk) p)` with the actual
// `a |-> b` asserts the implication at each posedge, its names those of the
// module, not the checker's formal a, bound to !a. a is high throughout and b
// until 32, so it holds at 5, 15 and 25 and fails at 35 and 45. The formal
// read as a variable, failing at every posedge.
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

// §17.3 with §16.5.1: the names a sequence actual reads are read sampled in
// the checker's assertion, as in an assertion written where the actual is. y
// is toggled by a nonblocking assignment at each posedge, so its sampled
// value is 1, 0, 1, 0, 1 at the five posedges and the value it takes there
// the opposite. The actual read the value y took.
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

// §17.3 with §23.3: a property actual reads the names of the instance
// writing it, in a call's arguments and a concatenation's elements too, so
// each of two instances of m gives its checker its own b: u1's high, where
// {a, b} holds two ones at the five posedges, and u2's low, where it holds
// one.
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

// The checker the procedural-instance cases share: one static concurrent
// assertion of a on clk, counting its successes and failures.
constexpr const char* kCountingChecker =
    "checker chk(logic a, logic clk);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
    "endchecker\n";

// The successes and failures `scope`'s counters hold once `module` has run
// over kCountingChecker.
std::pair<uint64_t, uint64_t> CheckerCounts(const std::string& module,
                                            const std::string& scope) {
  SimFixture f;
  auto* pass =
      RunAndFindVar(std::string(kCountingChecker) + module, f, scope + ".pass");
  if (pass == nullptr) return {~0ull, ~0ull};
  return {pass->value.ToUint64(),
          f.ctx.FindVariable(scope + ".fail")->value.ToUint64()};
}

// §17.3: a checker instantiated under an if in an always procedure is a
// procedural checker instance, its static concurrent assertion queued each
// time the statement is reached: clk rises at 5 to 45, en is low from 22 to
// 42, so the posedges at 25 and 35 queue nothing, and a, low from 12 to 32,
// fails at 15 alone.
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

// §17.3: reached once, after the posedge at 5 in an initial procedure, the
// instance queues one evaluation, which the tick at 5 begins; the failures
// a's low stretch would give later are never attempted.
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

// §17.3: a static instance of the same checker beside the procedural one is
// monitored at every posedge, and two procedural instances in one procedure
// keep their own queues: p1 and p2 are reached at every posedge but 25, s
// and p1 see a, s failing at 15 and 25 and p1 at 15 alone, and p2 sees b,
// low at 35 and 45.
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

// §17.3: everything in a procedural checker but its static assertions exists
// at every time step, so its always_ff counts all five posedges while its
// assertion, queued at the three where en is high, sees sum sampled at 0, 1
// and 4.
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

// §17.3 with §16.4.1: a static deferred assertion of a procedural checker is
// added to the pending deferred assertion report each time the statement is
// reached, at the posedges 5 to 35, its action calling the checker's own
// functions: a != b holds at 5 and 25 and fails at 15 and 35.
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

// §17.3: an interface's always procedure may instantiate a checker too: a
// fails at 15 and 25 and holds at the other three posedges.
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

// §17.3: a checker statically instantiated inside a procedural one has its
// static assertions treated as procedural ones, queued when the top-level
// ancestor's instantiation is reached, as in the first case.
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

// §17.3 with §17.2: a procedural instance may name a checker a package
// declares, found through the package scope as a static instance's is, and
// behaves as the first case's does.
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

}  // namespace
