#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

std::string Scoped(std::string_view scope, std::string_view name) {
  return scope.empty() ? std::string(name)
                       : std::string(scope) + "." + std::string(name);
}

void ExpectSameCounts(SimFixture& f, std::string_view checker,
                      std::string_view design) {
  for (std::string_view count : {"p", "f"}) {
    SCOPED_TRACE(count);
    uint64_t in_design = ValueOf(f, Scoped(design, count));
    EXPECT_GT(in_design, 0u) << design;
    EXPECT_EQ(ValueOf(f, Scoped(checker, count)), in_design) << checker;
  }
}

std::string Stimulus(const std::string& units, const std::string& items) {
  return units +
         "module top;\n"
         "  logic clk = 0, a = 0, b = 0, ba = 0, bb = 0;\n"
         "  bit [3:0] cnt = 4'd0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) begin\n"
         "    cnt <= cnt + 4'd1;\n"
         "    a <= cnt[0];\n"
         "    b <= cnt[1] ^ cnt[2];\n"
         "    ba = cnt[1];\n"
         "    bb = cnt[0] ^ cnt[2];\n"
         "  end\n" +
         items +
         "  initial #300 $finish;\n"
         "endmodule\n";
}

std::string CheckerAround(const std::string& items) {
  return "checker chk(logic clk, logic a, logic b);\n"
         "  int p = 0, f = 0;\n" +
         items + "endchecker\n";
}

constexpr std::string_view kImplication =
    "  a1: assert property (@(posedge clk) a |=> b) p++; else f++;\n";

std::string DesignBeside(const std::string& assertion,
                         const std::string& actuals) {
  return "  int p = 0, f = 0;\n" + assertion + "  chk c(" + actuals + ");\n";
}

TEST(CheckerConcurrentAssertionScheduling, NonblockingDrivenOperandsAgree) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                Stimulus(CheckerAround(std::string(kImplication)),
                         DesignBeside(std::string(kImplication), "clk, a, b")),
                f, "c.p"),
            nullptr);
  ExpectSameCounts(f, "c", "");
}

TEST(CheckerConcurrentAssertionScheduling, BlockingDrivenOperandsAgree) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                Stimulus(CheckerAround(std::string(kImplication)),
                         DesignBeside("  a1: assert property (@(posedge clk) "
                                      "ba |=> bb) p++; else f++;\n",
                                      "clk, ba, bb")),
                f, "c.p"),
            nullptr);
  ExpectSameCounts(f, "c", "");
}

TEST(CheckerConcurrentAssertionScheduling, ContinuouslyDrivenOperandsAgree) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(
          Stimulus(CheckerAround(std::string(kImplication)),
                   "  logic w;\n"
                   "  assign w = a ^ cnt[2];\n" +
                       DesignBeside("  a1: assert property (@(posedge clk) "
                                    "w |=> b) p++; else f++;\n",
                                    "clk, w, b")),
          f, "c.p"),
      nullptr);
  ExpectSameCounts(f, "c", "");
}

TEST(CheckerConcurrentAssertionScheduling, AssumptionsAgree) {
  constexpr std::string_view kAssumed =
      "  u1: assume property (@(posedge clk) a |=> b) p++; else f++;\n";
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(Stimulus(CheckerAround(std::string(kAssumed)),
                             DesignBeside(std::string(kAssumed), "clk, a, b")),
                    f, "c.p"),
      nullptr);
  ExpectSameCounts(f, "c", "");
}

TEST(CheckerConcurrentAssertionScheduling, CoverPropertyAndSequenceHitsAgree) {
  constexpr std::string_view kCovered =
      "  int hp = 0, hs = 0;\n"
      "  c1: cover property (@(posedge clk) a ##1 b) hp++;\n"
      "  c2: cover sequence (@(posedge clk) a ##1 b) hs++;\n";
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(Stimulus(CheckerAround(std::string(kCovered)),
                             std::string(kCovered) + "  chk c(clk, a, b);\n"),
                    f, "c.hp"),
      nullptr);
  for (std::string_view hits : {"hp", "hs"}) {
    SCOPED_TRACE(hits);
    uint64_t in_design = ValueOf(f, hits);
    EXPECT_GT(in_design, 0u);
    EXPECT_EQ(ValueOf(f, Scoped("c", hits)), in_design);
  }
}

TEST(CheckerConcurrentAssertionScheduling,
     AClockFromAContinuousAssignmentAgreesInEitherRegion) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(
          Stimulus(CheckerAround("  bit ck2;\n"
                                 "  assign ck2 = clk;\n"
                                 "  a1: assert property (@(posedge ck2) "
                                 "a |=> b) p++; else f++;\n"),
                   "  logic mck;\n"
                   "  assign mck = clk;\n" +
                       DesignBeside("  a1: assert property (@(posedge mck) "
                                    "a |=> b) p++; else f++;\n",
                                    "clk, a, b")),
          f, "c.p"),
      nullptr);
  ExpectSameCounts(f, "c", "");
}

TEST(CheckerConcurrentAssertionScheduling,
     AVariableFromAnAlwaysFfAgreesInEitherRegion) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(
          Stimulus(CheckerAround("  bit q;\n"
                                 "  always_ff @(posedge clk) q <= a;\n"
                                 "  a1: assert property (@(posedge clk) "
                                 "q |-> b) p++; else f++;\n"),
                   "  logic q;\n"
                   "  always_ff @(posedge clk) q <= a;\n" +
                       DesignBeside("  a1: assert property (@(posedge clk) "
                                    "q |-> b) p++; else f++;\n",
                                    "clk, a, b")),
          f, "c.p"),
      nullptr);
  ExpectSameCounts(f, "c", "");
}

TEST(CheckerConcurrentAssertionScheduling,
     ActionsReadTheNonblockingUpdateInBothPlaces) {
  constexpr std::string_view kSumming =
      "  int sum = 0;\n"
      "  a1: assert property (@(posedge clk) 1'b1) sum = sum + v;\n";
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                Stimulus("checker chk(logic clk, bit [3:0] v);\n" +
                             std::string(kSumming) + "endchecker\n",
                         "  bit [3:0] v;\n"
                         "  assign v = cnt;\n" +
                             std::string(kSumming) + "  chk c(clk, cnt);\n"),
                f, "c.sum"),
            nullptr);
  uint64_t in_design = ValueOf(f, "sum");
  EXPECT_EQ(in_design, 225u);
  EXPECT_EQ(ValueOf(f, "c.sum"), in_design);
}

TEST(CheckerConcurrentAssertionScheduling,
     EveryInstantiationScopeAgreesWithItsOwnAssertion) {
  std::string scoped = "  int p = 0, f = 0;\n" + std::string(kImplication) +
                       "  chk c(clk, a, b);\n";
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                Stimulus(CheckerAround(std::string(kImplication)) +
                             "interface ifc(input logic clk, input logic a,\n"
                             "              input logic b);\n" +
                             scoped +
                             "endinterface\n"
                             "program pr(input logic clk, input logic a,\n"
                             "           input logic b);\n" +
                             scoped +
                             "endprogram\n"
                             "checker outer(logic clk, logic a, logic b);\n" +
                             scoped + "endchecker\n",
                         "  ifc i(clk, a, b);\n"
                         "  pr pg(clk, a, b);\n"
                         "  outer o(clk, a, b);\n"
                         "  if (1) begin : g\n" +
                             scoped + "  end\n"),
                f, "i.c.p"),
            nullptr);
  for (std::string_view scope : {"i", "pg", "o", "g"}) {
    SCOPED_TRACE(scope);
    ExpectSameCounts(f, Scoped(scope, "c"), scope);
  }
}

TEST(CheckerConcurrentAssertionScheduling,
     AProceduralInstanceAgreesWithAProceduralAssertion) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(Stimulus(CheckerAround(std::string(kImplication)),
                                   "  int p = 0, f = 0;\n"
                                   "  always @(posedge clk) begin\n"
                                   "    a1: assert property (a |=> b) p++; "
                                   "else f++;\n"
                                   "    chk c(clk, a, b);\n"
                                   "  end\n"),
                          f, "c.p"),
            nullptr);
  ExpectSameCounts(f, "c", "");
}

}  // namespace
