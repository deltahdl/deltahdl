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

std::string ChangeWatcher(const std::string& allowed) {
  return "  int between = 0, after = 0;\n"
         "  bit [7:0] last, ors = 8'h00, ands = 8'hff;\n"
         "  always_ff @(posedge fclk) begin\n"
         "    if ($time > 45 && y != last) begin\n"
         "      if (" +
         allowed +
         ") after <= after + 1;\n"
         "      else between <= between + 1;\n"
         "    end\n"
         "    if ($time > 45) begin\n"
         "      ors <= ors | y;\n"
         "      ands <= ands & y;\n"
         "    end\n"
         "    last <= y;\n"
         "  end\n";
}

constexpr std::string_view kAfterClk = "$time % 40 == 25";
constexpr std::string_view kAfterEither =
    "$time % 40 == 25 || $time % 40 == 35";

std::string Clocks(const std::string& units, const std::string& instance) {
  return units +
         "module top;\n"
         "  logic clk = 0, clk2 = 0, fclk = 0;\n"
         "  int b = 0;\n"
         "  initial begin #20; forever begin clk = 1; #20 clk = 0; #20; end "
         "end\n"
         "  initial begin #30; forever begin clk2 = 1; #20 clk2 = 0; #20; end "
         "end\n"
         "  always #5 fclk = ~fclk;\n"
         "  always @(posedge clk) b = b + 1;\n" +
         instance +
         "  initial #800 $finish;\n"
         "endmodule\n";
}

std::string Watched(const std::string& items, const std::string& allowed) {
  return "checker chk(logic clk, logic clk2, logic fclk, int b);\n"
         "  rand bit [7:0] x, y;\n" +
         items + ChangeWatcher(allowed) + "endchecker\n";
}

constexpr std::string_view kTracksB =
    "  m1: assume property (@(posedge clk) x == 8'(b) + 8'd100);\n";

constexpr std::string_view kInstance = "  chk c(clk, clk2, fclk, b);\n";

void ExpectChangesOnlyAfterEvents(SimFixture& f, std::string_view scope) {
  EXPECT_EQ(ValueOf(f, std::string(scope) + ".between"), 0u);
  EXPECT_GT(ValueOf(f, std::string(scope) + ".after"), 10u);
}

TEST(AbsentActiveVariable, ChangesOnlyAtAssumeSetClockEvents) {
  SimFixture f;
  RunDesign(f,
            Clocks(Watched(std::string(kTracksB), std::string(kAfterClk)),
                   std::string(kInstance)),
            "c.between");
  ExpectChangesOnlyAfterEvents(f, "c");
}

TEST(AbsentActiveVariable, StaysUnconstrainedAcrossTheEvents) {
  SimFixture f;
  RunDesign(f,
            Clocks(Watched(std::string(kTracksB), std::string(kAfterClk)),
                   std::string(kInstance)),
            "c.ors");
  EXPECT_EQ(ValueOf(f, "c.ors"), 0xffu);
  EXPECT_EQ(ValueOf(f, "c.ands"), 0u);
}

TEST(AbsentActiveVariable, TheAssumedVariableBesideItMeetsItsAssumption) {
  SimFixture f;
  RunDesign(f,
            Clocks(Watched(std::string(kTracksB) +
                               "  int fail = 0;\n"
                               "  a1: assert property (@(posedge clk)\n"
                               "    x == 8'(b) + 8'd100) else fail++;\n",
                           std::string(kAfterClk)),
                   std::string(kInstance)),
            "c.fail");
  EXPECT_EQ(ValueOf(f, "c.fail"), 0u);
  EXPECT_EQ(ValueOf(f, "c.x"), 119u);
}

TEST(AbsentActiveVariable, TwoClocksLetItChangeAfterEventsOfEither) {
  SimFixture f;
  RunDesign(f,
            Clocks(Watched(std::string(kTracksB) +
                               "  rand bit [7:0] z;\n"
                               "  m2: assume property (@(posedge clk2) "
                               "z != 8'd0);\n",
                           std::string(kAfterEither)),
                   std::string(kInstance)),
            "c.between");
  EXPECT_EQ(ValueOf(f, "c.between"), 0u);
  EXPECT_GT(ValueOf(f, "c.after"), 20u);
}

TEST(AbsentActiveVariable, AnAssertionOrCoverReadingItLeavesItUnconstrained) {
  SimFixture f;
  RunDesign(f,
            Clocks(Watched(std::string(kTracksB) +
                               "  a1: assert property (@(posedge clk) "
                               "y == 8'd7);\n"
                               "  c1: cover property (@(posedge clk) "
                               "y == 8'd9);\n",
                           std::string(kAfterClk)),
                   std::string(kInstance)),
            "c.between");
  ExpectChangesOnlyAfterEvents(f, "c");
  EXPECT_EQ(ValueOf(f, "c.ors"), 0xffu);
  EXPECT_EQ(ValueOf(f, "c.ands"), 0u);
}

TEST(AbsentActiveVariable, AnAssumptionLeftOutByAConstCastDoesNotClockIt) {
  SimFixture f;
  RunDesign(f,
            Clocks("checker chk(logic clk, logic clk2, logic fclk, int b,\n"
                   "           bit [7:0] k);\n"
                   "  rand bit [7:0] x, y;\n" +
                       std::string(kTracksB) +
                       "  m2: assume property (@(posedge clk2) y == k);\n" +
                       ChangeWatcher(std::string(kAfterClk)) + "endchecker\n",
                   "  logic [7:0] k = 8'd3;\n"
                   "  chk c(clk, clk2, fclk, b, const'(k));\n"),
            "c.between");
  ExpectChangesOnlyAfterEvents(f, "c");
  EXPECT_EQ(ValueOf(f, "c.ors"), 0xffu);
  EXPECT_EQ(ValueOf(f, "c.ands"), 0u);
}

TEST(AbsentActiveVariable, AChildsAssumptionAloneClocksTheParent) {
  SimFixture f;
  RunDesign(f,
            Clocks("checker kid(logic clk, bit [7:0] v, int b);\n"
                   "  u1: assume property (@(posedge clk) v == 8'(b));\n"
                   "endchecker\n" +
                       Watched("  kid k(clk, x, b);\n", std::string(kAfterClk)),
                   std::string(kInstance)),
            "c.between");
  ExpectChangesOnlyAfterEvents(f, "c");
}

TEST(AbsentActiveVariable, EveryInstantiationPlaceClocksItTheSameWay) {
  SimFixture f;
  RunDesign(f,
            Clocks(Watched(std::string(kTracksB), std::string(kAfterClk)) +
                       "interface ifc(input logic clk, input logic clk2,\n"
                       "              input logic fclk, input var int b);\n"
                       "  chk c(clk, clk2, fclk, b);\n"
                       "endinterface\n"
                       "program pr(input logic clk, input logic clk2,\n"
                       "           input logic fclk, input var int b);\n"
                       "  chk c(clk, clk2, fclk, b);\n"
                       "endprogram\n",
                   "  ifc i(clk, clk2, fclk, b);\n"
                   "  pr p(clk, clk2, fclk, b);\n"
                   "  always @(posedge fclk) chk c(clk, clk2, fclk, b);\n"),
            "i.c.between");
  for (std::string_view scope : {"i.c", "p.c", "c"}) {
    SCOPED_TRACE(scope);
    ExpectChangesOnlyAfterEvents(f, scope);
  }
}

}  // namespace
