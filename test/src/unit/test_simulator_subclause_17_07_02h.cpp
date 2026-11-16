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

void RunDesign(SimFixture& f, const std::string& src, std::string_view first) {
  ASSERT_NE(RunAndFindVar(src, f, first), nullptr);
}

std::string InTop(const std::string& units, const std::string& instance,
                  int end = 60) {
  return units +
         "module top;\n"
         "  logic clk = 0;\n"
         "  always #5 clk = ~clk;\n" +
         instance + "  initial #" + std::to_string(end) +
         " $finish;\n"
         "endmodule\n";
}

void ExpectCounts(SimFixture& f, std::string_view scope, uint64_t pass,
                  uint64_t fail) {
  EXPECT_EQ(ValueOf(f, std::string(scope) + ".pass"), pass) << scope;
  EXPECT_EQ(ValueOf(f, std::string(scope) + ".fail"), fail) << scope;
}

constexpr std::string_view kAssertingKid =
    "checker kid(logic clk, bit [7:0] x);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@(posedge clk) x == 8'd42) pass++; "
    "else fail++;\n"
    "endchecker\n";

constexpr std::string_view kAssumingKid =
    "checker kid(logic clk, bit [7:0] x);\n"
    "  int pass = 0, fail = 0;\n"
    "  u1: assume property (@(posedge clk) x == 8'd42) pass++; "
    "else fail++;\n"
    "  int apass = 0, afail = 0;\n"
    "  a1: assert property (@(posedge clk) x == 8'd42) apass++; "
    "else afail++;\n"
    "endchecker\n";

TEST(ParentSolvedValueThroughAFormal, AnOwnImmediateAssertionReadsIt) {
  SimFixture f;
  RunDesign(f,
            InTop("checker chk(logic clk);\n"
                  "  rand bit [7:0] q;\n"
                  "  m1: assume property (@(posedge clk) q == 8'd42);\n"
                  "  int pass = 0, fail = 0;\n"
                  "  always_ff @(posedge clk)\n"
                  "    a1: assert (q == 8'd42) pass <= pass + 1;\n"
                  "    else fail <= fail + 1;\n"
                  "endchecker\n",
                  "  chk c(clk);\n"),
            "c.pass");
  ExpectCounts(f, "c", 6, 0);
}

TEST(ParentSolvedValueThroughAFormal,
     DISABLED_AChildsAssertionReadsItWhenTheParentAssumes) {
  SimFixture f;
  RunDesign(f,
            InTop(std::string(kAssertingKid) +
                      "checker chk(logic clk);\n"
                      "  rand bit [7:0] q;\n"
                      "  kid k(clk, q);\n"
                      "  u1: assume property (@(posedge clk) q == 8'd42);\n"
                      "endchecker\n",
                  "  chk c(clk);\n"),
            "c.k.pass");
  ExpectCounts(f, "c.k", 6, 0);
}

TEST(ParentSolvedValueThroughAFormal,
     DISABLED_AChildsOwnAssumptionIsMetAndItsAssertionReadsIt) {
  SimFixture f;
  RunDesign(f,
            InTop(std::string(kAssumingKid) + "checker chk(logic clk);\n"
                                              "  rand bit [7:0] q;\n"
                                              "  kid k(clk, q);\n"
                                              "endchecker\n",
                  "  chk c(clk);\n"),
            "c.k.pass");
  ExpectCounts(f, "c.k", 6, 0);
  EXPECT_EQ(ValueOf(f, "c.k.apass"), 6u);
  EXPECT_EQ(ValueOf(f, "c.k.afail"), 0u);
}

TEST(ParentSolvedValueThroughAFormal,
     DISABLED_AChildsAlwaysFfAndItsImmediateAssertionReadIt) {
  SimFixture f;
  RunDesign(f,
            InTop("checker kid(logic clk, bit [7:0] x);\n"
                  "  bit [7:0] h;\n"
                  "  int pass = 0, fail = 0;\n"
                  "  always_ff @(posedge clk) begin\n"
                  "    h <= x;\n"
                  "    a1: assert (x == 8'd42) pass <= pass + 1;\n"
                  "    else fail <= fail + 1;\n"
                  "  end\n"
                  "endchecker\n"
                  "checker chk(logic clk);\n"
                  "  rand bit [7:0] q;\n"
                  "  m1: assume property (@(posedge clk) q == 8'd42);\n"
                  "  kid k(clk, q);\n"
                  "endchecker\n",
                  "  chk c(clk);\n"),
            "c.k.pass");
  ExpectCounts(f, "c.k", 6, 0);
  EXPECT_EQ(ValueOf(f, "c.k.h"), 42u);
}

TEST(ParentSolvedValueThroughAFormal,
     DISABLED_AMiddleCheckerAndAGrandchildReadIt) {
  SimFixture f;
  RunDesign(
      f,
      InTop(std::string(kAssertingKid) +
                "checker mid(logic clk, bit [7:0] y);\n"
                "  int pass = 0, fail = 0;\n"
                "  a1: assert property (@(posedge clk) y == 8'd42) pass++; "
                "else fail++;\n"
                "  kid k(clk, y);\n"
                "endchecker\n"
                "checker chk(logic clk);\n"
                "  rand bit [7:0] q;\n"
                "  m1: assume property (@(posedge clk) q == 8'd42);\n"
                "  mid m(clk, q);\n"
                "endchecker\n",
            "  chk c(clk);\n"),
      "c.m.pass");
  ExpectCounts(f, "c.m", 6, 0);
  ExpectCounts(f, "c.m.k", 6, 0);
}

TEST(ParentSolvedValueThroughAFormal,
     DISABLED_AnActualOverTwoActiveVariablesIsRead) {
  SimFixture f;
  RunDesign(f,
            InTop(std::string(kAssertingKid) +
                      "checker chk(logic clk);\n"
                      "  rand bit [7:0] q, r;\n"
                      "  m1: assume property (@(posedge clk) "
                      "q == 8'd40 && r == 8'd2);\n"
                      "  kid k(clk, q + r);\n"
                      "endchecker\n",
                  "  chk c(clk);\n"),
            "c.k.pass");
  ExpectCounts(f, "c.k", 6, 0);
}

TEST(ParentSolvedValueThroughAFormal,
     DISABLED_AChildInTheGenerateBlockDeclaringTheVariableReadsIt) {
  SimFixture f;
  RunDesign(f,
            InTop(std::string(kAssertingKid) +
                      "checker chk(logic clk);\n"
                      "  if (1) begin : g\n"
                      "    rand bit [7:0] q;\n"
                      "    m1: assume property (@(posedge clk) q == 8'd42);\n"
                      "    kid k(clk, q);\n"
                      "  end\n"
                      "endchecker\n",
                  "  chk c(clk);\n"),
            "c.g.k.pass");
  ExpectCounts(f, "c.g.k", 6, 0);
}

TEST(ParentSolvedValueThroughAFormal, TheSolveReadsSampledValuesOfOthers) {
  SimFixture f;
  RunDesign(f,
            "checker chk(logic clk, bit [7:0] a);\n"
            "  rand bit [7:0] q;\n"
            "  m1: assume property (@(posedge clk) q == a);\n"
            "endchecker\n"
            "module top;\n"
            "  logic clk = 0;\n"
            "  bit [7:0] a = 8'd10;\n"
            "  always #5 clk = ~clk;\n"
            "  always @(posedge clk) a <= a + 8'd1;\n"
            "  chk c(clk, a);\n"
            "  initial #42 $finish;\n"
            "endmodule\n",
            "c.q");
  EXPECT_EQ(ValueOf(f, "a"), 14u);
  EXPECT_EQ(ValueOf(f, "c.q"), 13u);
}

constexpr std::string_view kSelfChecking =
    "checker chk(logic clk);\n"
    "  rand bit [7:0] q;\n"
    "  m1: assume property (@(posedge clk) q == 8'd42);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@(posedge clk) q == 8'd42) pass++; "
    "else fail++;\n"
    "endchecker\n";

TEST(ParentSolvedValueThroughAFormal, EveryInstantiationPlaceReadsItsValue) {
  SimFixture f;
  RunDesign(
      f,
      InTop(std::string(kSelfChecking) + "interface ifc(input logic clk);\n"
                                         "  chk c(clk);\n"
                                         "endinterface\n"
                                         "program pr(input logic clk);\n"
                                         "  chk c(clk);\n"
                                         "endprogram\n",
            "  ifc i(clk);\n"
            "  pr p(clk);\n"
            "  always @(posedge clk) chk c(clk);\n"),
      "i.c.pass");
  ExpectCounts(f, "i.c", 6, 0);
  ExpectCounts(f, "p.c", 6, 0);
  EXPECT_EQ(ValueOf(f, "c.fail"), 0u);
  EXPECT_GT(ValueOf(f, "c.pass"), 0u);
}

TEST(ParentSolvedValueThroughAFormal, ANonFreeVariableActualFollowsEachValue) {
  SimFixture f;
  RunDesign(f,
            InTop("checker kid(logic clk, bit [7:0] x);\n"
                  "  bit [7:0] h;\n"
                  "  int pass = 0, fail = 0;\n"
                  "  always_ff @(posedge clk) h <= x;\n"
                  "  a1: assert property (@(posedge clk) x == h + 8'd1 || "
                  "x == 8'd0) pass++; else fail++;\n"
                  "endchecker\n"
                  "checker chk(logic clk);\n"
                  "  bit [7:0] n = 8'd0;\n"
                  "  always_ff @(posedge clk) n <= n + 8'd1;\n"
                  "  kid k(clk, n);\n"
                  "endchecker\n",
                  "  chk c(clk);\n"),
            "c.k.h");
  EXPECT_EQ(ValueOf(f, "c.k.h"), 5u);
  EXPECT_EQ(ValueOf(f, "c.k.fail"), 0u);
}

}  // namespace
