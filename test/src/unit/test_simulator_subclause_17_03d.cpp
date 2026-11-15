#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::vector<uint64_t> Values(const std::string& src,
                             const std::vector<std::string>& names) {
  SimFixture f;
  if (RunAndFindVar(src, f, names.front()) == nullptr) return {};
  std::vector<uint64_t> values;
  for (const auto& name : names) {
    auto* var = f.ctx.FindVariable(name);
    values.push_back(var == nullptr ? ~0ull : var->value.ToUint64());
  }
  return values;
}

std::vector<std::string> In(const std::string& scope,
                            const std::vector<std::string>& names) {
  std::vector<std::string> paths;
  for (const auto& name : names) {
    std::string path = scope;
    path += ".";
    path += name;
    paths.push_back(path);
  }
  return paths;
}

const char* const kLoopChecker =
    "checker c2(logic clk, logic [7:0] a);\n"
    "  logic [7:0] sum = 0, dbl;\n"
    "  int init = 10, pp = 0, p0p = 0, p0f = 0;\n"
    "  always_ff @(posedge clk) begin\n"
    "    sum <= sum + a;\n"
    "    init <= init + 1;\n"
    "    p0: assert property (sum < 3) p0p++; else p0f++;\n"
    "  end\n"
    "  always_comb dbl = a * 2;\n"
    "  p1: assert property (@(posedge clk) sum < 100) pp++;\n"
    "endchecker\n";

const char* const kLoopClock =
    "  logic clk = 0;\n"
    "  logic [7:0] in1 = 1;\n"
    "  always #5 clk = ~clk;\n"
    "  initial begin #12 in1 = 7; #6 in1 = 1; #34 $finish; end\n";

std::vector<std::string> LoopNames() {
  return {"sum", "init", "p0p", "p0f", "pp", "dbl"};
}

TEST(CheckerContentsPerInstance, ALoopedInstanceKeepsOneCopy) {
  EXPECT_EQ(Values(std::string(kLoopChecker) + "module top;\n" + kLoopClock +
                       "  always @(posedge clk)\n"
                       "    for (int i = 0; i < 4; i++)\n"
                       "      if (i != 2) c2 check_loop(clk, in1);\n"
                       "endmodule\n",
                   In("check_loop", LoopNames())),
            (std::vector<uint64_t>{11, 15, 2, 3, 15, 2}));
}

TEST(CheckerContentsPerInstance, AnInterfaceLoopKeepsOneCopy) {
  EXPECT_EQ(Values(std::string(kLoopChecker) +
                       "interface ifc(input logic clk, input logic [7:0] "
                       "in1);\n"
                       "  always @(posedge clk)\n"
                       "    for (int i = 0; i < 3; i++) c2 k(clk, in1);\n"
                       "endinterface\n"
                       "module top;\n" +
                       kLoopClock + "  ifc i(clk, in1);\nendmodule\n",
                   In("i.k", LoopNames())),
            (std::vector<uint64_t>{11, 15, 2, 3, 15, 2}));
}

TEST(CheckerContentsPerInstance, AGenerateLoopMakesACopyPerIteration) {
  std::string src = std::string(kLoopChecker) + "module top;\n" + kLoopClock +
                    "  for (genvar g = 0; g < 3; g++) begin : gl\n"
                    "    c2 k(clk, in1 + g);\n"
                    "  end\n"
                    "endmodule\n";
  EXPECT_EQ(Values(src, {"gl[0].k.sum", "gl[1].k.sum", "gl[2].k.sum",
                         "gl[0].k.init", "gl[2].k.dbl"}),
            (std::vector<uint64_t>{11, 16, 21, 15, 6}));
}

const char* const kLatchChecker =
    "checker c3(logic clk, logic [7:0] a, logic g);\n"
    "  int ticks = 0;\n"
    "  logic [7:0] cb, lt;\n"
    "  always_ff @(posedge clk) ticks <= ticks + 1;\n"
    "  always_comb cb = a + 1;\n"
    "  always_latch if (g) lt = a;\n"
    "endchecker\n";

std::string LatchTop(const std::string& procedure) {
  return std::string(kLatchChecker) +
         "module top;\n"
         "  logic clk = 0, g = 1, en = 0;\n"
         "  logic [7:0] a = 1;\n"
         "  always #5 clk = ~clk;\n" +
         procedure +
         "  initial begin #12 a = 7; #8 g = 0; #5 a = 9; #27 $finish; end\n"
         "endmodule\n";
}

std::vector<std::string> LatchNames() { return {"c.ticks", "c.cb", "c.lt"}; }

TEST(CheckerContentsPerInstance, AnInstanceNeverReachedStillRuns) {
  EXPECT_EQ(Values(LatchTop("  always @(posedge clk) begin\n"
                            "    if (en) c3 c(clk, a, g);\n"
                            "  end\n"),
                   LatchNames()),
            (std::vector<uint64_t>{5, 10, 7}));
}

TEST(CheckerContentsPerInstance, AnInstanceReachedOnceInAnInitialRuns) {
  EXPECT_EQ(Values(LatchTop("  initial begin\n"
                            "    c3 c(clk, a, g);\n"
                            "  end\n"),
                   LatchNames()),
            (std::vector<uint64_t>{5, 10, 7}));
}

const char* const kDeferredCounters =
    "  int ap = 0, af = 0, fp = 0, ff = 0, c0 = 0, cf = 0;\n"
    "  int mp = 0, mf = 0, np = 0, nf = 0;\n"
    "  function void inc_ap(); ap++; endfunction\n"
    "  function void inc_af(); af++; endfunction\n"
    "  function void inc_fp(); fp++; endfunction\n"
    "  function void inc_ff(); ff++; endfunction\n"
    "  function void inc_c0(); c0++; endfunction\n"
    "  function void inc_cf(); cf++; endfunction\n"
    "  function void inc_mp(); mp++; endfunction\n"
    "  function void inc_mf(); mf++; endfunction\n"
    "  function void inc_np(); np++; endfunction\n"
    "  function void inc_nf(); nf++; endfunction\n";

std::vector<std::string> DeferredNames() {
  return {"ap", "af", "fp", "ff", "c0", "cf", "mp", "mf", "np", "nf"};
}

TEST(CheckerStaticAssertionPlacement,
     AStaticInstancesDeferredFormsRunOnChange) {
  EXPECT_EQ(
      Values("checker oh(logic [3:0] a);\n" + std::string(kDeferredCounters) +
                 "  d1: assert #0 ($onehot(a)) inc_ap(); else inc_af();\n"
                 "  d2: assert final ($onehot(a)) inc_fp(); else "
                 "inc_ff();\n"
                 "  d3: cover #0 ($onehot(a)) inc_c0();\n"
                 "  d4: cover final ($onehot(a)) inc_cf();\n"
                 "  d5: assume #0 ($onehot(a)) inc_mp(); else inc_mf();\n"
                 "  d6: assume final ($onehot(a)) inc_np(); else "
                 "inc_nf();\n"
                 "endchecker\n"
                 "module top;\n"
                 "  logic [3:0] a = 4'b0001;\n"
                 "  oh u(a);\n"
                 "  initial begin\n"
                 "    #2 a = 4'b0010;\n"
                 "    #1 a = 4'b0011;\n"
                 "    #1 a = 4'b0100;\n"
                 "    #2 $finish;\n"
                 "  end\n"
                 "endmodule\n",
             In("u", DeferredNames())),
      (std::vector<uint64_t>{3, 1, 3, 1, 3, 3, 3, 1, 3, 1}));
}

std::string DeferredChecker() {
  return "checker dc(logic a, b);\n" + std::string(kDeferredCounters) +
         "  d1: assert #0 (a != b) inc_ap(); else inc_af();\n"
         "  d2: assert final (a != b) inc_fp(); else inc_ff();\n"
         "  d3: cover #0 (a == b) inc_c0();\n"
         "  d4: cover final (a == b) inc_cf();\n"
         "  d5: assume #0 (a != b) inc_mp(); else inc_mf();\n"
         "  d6: assume final (a != b) inc_np(); else inc_nf();\n"
         "endchecker\n";
}

std::string DeferredTop(const std::string& checkers,
                        const std::string& instance) {
  return DeferredChecker() + checkers +
         "module top;\n"
         "  logic clk = 0, a = 1, b = 0;\n"
         "  always #5 clk = ~clk;\n" +
         instance +
         "  initial begin #10 a = 0; #2 b = 1; #8 a = 1; #10 b = 0; #10 "
         "$finish; end\n"
         "endmodule\n";
}

std::vector<uint64_t> ReachedAtEdges() {
  return {3, 1, 3, 1, 1, 1, 3, 1, 3, 1};
}
std::vector<uint64_t> OnEveryChange() { return {3, 2, 3, 2, 2, 2, 3, 2, 3, 2}; }

TEST(CheckerStaticAssertionPlacement,
     AStaticInstancesDeferredFormsSeeEachChange) {
  EXPECT_EQ(
      Values(DeferredTop("", "  dc u(a, b);\n"), In("u", DeferredNames())),
      OnEveryChange());
}

TEST(CheckerStaticAssertionPlacement,
     AProceduralInstancesDeferredFormsRunWhenReached) {
  EXPECT_EQ(Values(DeferredTop("",
                               "  always @(posedge clk) begin\n"
                               "    dc u(a, b);\n"
                               "  end\n"),
                   In("u", DeferredNames())),
            ReachedAtEdges());
}

const char* const kOuterDeferred =
    "checker outer(logic a, b);\n"
    "  dc i(a, b);\n"
    "endchecker\n";

TEST(CheckerStaticAssertionPlacement,
     ANestedDeferredFormFollowsAProceduralAncestor) {
  EXPECT_EQ(Values(DeferredTop(kOuterDeferred,
                               "  always @(posedge clk) begin\n"
                               "    outer o(a, b);\n"
                               "  end\n"),
                   In("o.i", DeferredNames())),
            ReachedAtEdges());
}

TEST(CheckerStaticAssertionPlacement,
     ANestedDeferredFormFollowsAStaticAncestor) {
  EXPECT_EQ(Values(DeferredTop(kOuterDeferred, "  outer o(a, b);\n"),
                   In("o.i", DeferredNames())),
            OnEveryChange());
}

const char* const kMixedChecker =
    "checker mix(logic a, b, logic clk);\n"
    "  int cp = 0, cf = 0, dp = 0, df = 0, cv = 0, mp = 0, mf = 0;\n"
    "  function void inc_dp(); dp++; endfunction\n"
    "  function void inc_df(); df++; endfunction\n"
    "  c1: assert property (@(posedge clk) a != b) cp++; else cf++;\n"
    "  c2: cover property (@(posedge clk) a) cv++;\n"
    "  c3: assume property (@(posedge clk) a != b) mp++; else mf++;\n"
    "  d1: assert #0 (a != b) inc_dp(); else inc_df();\n"
    "endchecker\n"
    "checker mid(logic a, b, logic clk);\n"
    "  mix m(a, b, clk);\n"
    "endchecker\n"
    "checker top2(logic a, b, logic clk);\n"
    "  mid d(a, b, clk);\n"
    "endchecker\n";

std::string MixedTop(const std::string& instance) {
  return std::string(kMixedChecker) +
         "module top;\n"
         "  logic clk = 0, a = 1, b = 0, en = 1;\n"
         "  always #5 clk = ~clk;\n" +
         instance +
         "  initial begin #10 a = 0; #2 b = 1; #8 a = 1; #2 en = 0; #6 en = 1; "
         "#2 b = 0; #10 $finish; end\n"
         "endmodule\n";
}

std::vector<std::string> MixedNames() {
  return {"cp", "cf", "cv", "mp", "mf", "dp", "df"};
}

TEST(CheckerStaticAssertionPlacement,
     AProceduralInstancesCoverAndAssumeAreQueuedWhenReached) {
  EXPECT_EQ(Values(MixedTop("  always @(posedge clk) begin\n"
                            "    if (en) mix u(a, b, clk);\n"
                            "  end\n"),
                   In("u", MixedNames())),
            (std::vector<uint64_t>{3, 0, 2, 3, 0, 3, 0}));
}

TEST(CheckerStaticAssertionPlacement, TwoLevelsDeepFollowAProceduralAncestor) {
  EXPECT_EQ(Values(MixedTop("  always @(posedge clk) begin\n"
                            "    if (en) top2 t(a, b, clk);\n"
                            "  end\n"),
                   In("t.d.m", MixedNames())),
            (std::vector<uint64_t>{3, 0, 2, 3, 0, 3, 0}));
}

TEST(CheckerStaticAssertionPlacement, TwoLevelsDeepFollowAStaticAncestor) {
  EXPECT_EQ(
      Values(MixedTop("  top2 t(a, b, clk);\n"), In("t.d.m", MixedNames())),
      (std::vector<uint64_t>{3, 1, 3, 3, 1, 3, 2}));
}

TEST(CheckerStaticAssertionPlacement,
     ReenteringTheProcedureFlushesAQueuedConcurrentAssertion) {
  EXPECT_EQ(Values(std::string(kMixedChecker) +
                       "module top;\n"
                       "  logic clk = 0, a = 1, b = 0, x = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  always @(posedge clk) x <= ~x;\n"
                       "  always @(posedge clk or x) begin\n"
                       "    if (clk) mix u(a, b, clk);\n"
                       "  end\n"
                       "  initial #52 $finish;\n"
                       "endmodule\n",
                   In("u", {"cp", "cf", "cv", "mp", "mf"})),
            (std::vector<uint64_t>{5, 0, 5, 5, 0}));
}

TEST(CheckerStaticAssertionPlacement,
     ReenteringTheProcedureFlushesAQueuedDeferredAssertion) {
  EXPECT_EQ(Values(DeferredChecker() + "module top;\n"
                                       "  logic x = 0, y = 0;\n"
                                       "  always @(x or y) begin\n"
                                       "    dc u(x, y);\n"
                                       "  end\n"
                                       "  initial begin\n"
                                       "    #5 x = 1; y <= 1;\n"
                                       "    #5 x = 0; y <= 0;\n"
                                       "    #5 $finish;\n"
                                       "  end\n"
                                       "endmodule\n",
                   In("u", DeferredNames())),
            (std::vector<uint64_t>{0, 2, 0, 2, 2, 2, 0, 2, 0, 2}));
}

}  // namespace
