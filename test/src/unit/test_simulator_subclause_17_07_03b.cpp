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

std::string WithEventAndUpdate(const std::string& units,
                               const std::string& items) {
  return units +
         "module top;\n"
         "  logic a = 0, b = 0;\n"
         "  event e;\n" +
         items +
         "  initial begin\n"
         "    #10 ->e; a = 1; b <= 1;\n"
         "    #10 ->e;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

TEST(CheckerReactiveScheduling,
     AnAlwaysFfOnANamedEventSeesItsSequenceTriggered) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                WithEventAndUpdate("checker chk(event e);\n"
                                   "  sequence s;\n"
                                   "    @(e) 1'b1;\n"
                                   "  endsequence\n"
                                   "  int hits = 0, misses = 0;\n"
                                   "  always_ff @(e)\n"
                                   "    if (s.triggered) hits <= hits + 1;\n"
                                   "    else misses <= misses + 1;\n"
                                   "endchecker\n",
                                   "  chk c(e);\n"),
                f, "c.hits"),
            nullptr);
  EXPECT_EQ(ValueOf(f, "c.hits"), 2u);
  EXPECT_EQ(ValueOf(f, "c.misses"), 0u);
}

TEST(CheckerReactiveScheduling,
     DISABLED_AnInitialOnAnEnclosingEventReadsTheUpdate) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  logic b = 0;\n"
      "  event e;\n"
      "  initial begin #10 ->e; b <= 1; #10 $finish; end\n"
      "  checker chk;\n"
      "    initial @(e) a1: assert (b == 1'b1) $display(\"after\");\n"
      "      else $display(\"before\");\n"
      "  endchecker\n"
      "  chk k();\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("after\n"), std::string::npos) << out;
  EXPECT_EQ(out.find("before\n"), std::string::npos) << out;
}

TEST(CheckerReactiveScheduling,
     DISABLED_AnInitialOnAnEventFormalReadsTheUpdate) {
  SimFixture f;
  std::string out = RunCapture(
      WithEventAndUpdate(
          "checker chk(event ev, logic b);\n"
          "  initial @(ev) a1: assert (b == 1'b1) $display(\"after\");\n"
          "    else $display(\"before\");\n"
          "endchecker\n",
          "  chk c(e, b);\n"),
      f);
  EXPECT_NE(out.find("after\n"), std::string::npos) << out;
  EXPECT_EQ(out.find("before\n"), std::string::npos) << out;
}

TEST(CheckerReactiveScheduling, AnInitialOnASignalEdgeReadsTheUpdate) {
  SimFixture f;
  std::string out = RunCapture(
      WithEventAndUpdate("checker chk(logic a, logic b);\n"
                         "  initial @(posedge a) a1: assert (b == 1'b1) "
                         "$display(\"after\");\n"
                         "    else $display(\"before\");\n"
                         "endchecker\n",
                         "  chk c(a, b);\n"),
      f);
  EXPECT_NE(out.find("after\n"), std::string::npos) << out;
  EXPECT_EQ(out.find("before\n"), std::string::npos) << out;
}

constexpr std::string_view kSettledReaders =
    "checker chk(logic a);\n"
    "  function automatic bit rd();\n"
    "    return a;\n"
    "  endfunction\n"
    "  bit dc, dl, da, df;\n"
    "  int nc = 0, nl = 0, na = 0, nf = 0;\n"
    "  always_comb dc = a;\n"
    "  always_latch if (1'b1) dl = a;\n"
    "  assign da = a;\n"
    "  always_comb df = rd();\n"
    "  always_ff @(dc) nc <= nc + 1;\n"
    "  always_ff @(dl) nl <= nl + 1;\n"
    "  always_ff @(da) na <= na + 1;\n"
    "  always_ff @(df) nf <= nf + 1;\n"
    "endchecker\n";

std::string Glitching(const std::string& units, const std::string& items) {
  return std::string(kSettledReaders) + units +
         "module top;\n"
         "  logic clk = 0, a = 0;\n"
         "  int na_mod = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(a) na_mod++;\n" +
         items +
         "  initial begin\n"
         "    #12 a = 1; a <= 0;\n"
         "    #20 $finish;\n"
         "  end\n"
         "endmodule\n";
}

void ExpectSettledOnly(SimFixture& f, std::string_view scope) {
  for (std::string_view count : {"nc", "nl", "na", "nf"}) {
    SCOPED_TRACE(count);
    EXPECT_EQ(ValueOf(f, std::string(scope) + "." + std::string(count)), 0u)
        << scope;
  }
}

TEST(CheckerReactiveScheduling,
     CombLatchAndContinuousReadersSeeTheSettledValue) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(Glitching("", "  chk c(a);\n"), f, "c.nc"), nullptr);
  EXPECT_EQ(ValueOf(f, "na_mod"), 2u);
  ExpectSettledOnly(f, "c");
}

TEST(CheckerReactiveScheduling, EveryInstantiationPlaceSeesTheSettledValue) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(Glitching("interface ifc(input logic a);\n"
                                    "  chk c(a);\n"
                                    "endinterface\n"
                                    "program pr(input logic a);\n"
                                    "  chk c(a);\n"
                                    "endprogram\n"
                                    "checker outer(logic a);\n"
                                    "  chk c(a);\n"
                                    "endchecker\n",
                                    "  ifc i(a);\n"
                                    "  pr p(a);\n"
                                    "  outer o(a);\n"
                                    "  if (1) begin : g\n"
                                    "    chk c(a);\n"
                                    "  end\n"
                                    "  always @(posedge clk) chk c(a);\n"),
                          f, "i.c.nc"),
            nullptr);
  for (std::string_view scope : {"i.c", "p.c", "o.c", "g.c", "c"}) {
    SCOPED_TRACE(scope);
    ExpectSettledOnly(f, scope);
  }
}

}  // namespace
