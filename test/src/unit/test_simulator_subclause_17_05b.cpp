#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_final_output.h"

using namespace delta;

namespace {

std::vector<uint64_t> Values(const std::string& src,
                             const std::vector<std::string>& names) {
  SimFixture f;
  std::vector<uint64_t> values;
  auto* first = RunAndFindVar(src, f, names.front());
  if (first == nullptr) return values;
  values.reserve(names.size());
  for (const auto& name : names) {
    auto* var = f.ctx.FindVariable(name);
    values.push_back(var == nullptr ? 99u : var->value.ToUint64());
  }
  return values;
}

std::vector<std::string> In(const std::string& scope,
                            const std::vector<std::string>& names) {
  std::vector<std::string> scoped;
  scoped.reserve(names.size());
  for (const auto& name : names) {
    std::string full = scope;
    full += '.';
    full += name;
    scoped.push_back(full);
  }
  return scoped;
}

const char* const kCounters =
    "  int ap = 0, af = 0, dp = 0, df = 0, fp = 0, ff = 0;\n"
    "  function void inc_ap(); ap++; endfunction\n"
    "  function void inc_af(); af++; endfunction\n"
    "  function void inc_dp(); dp++; endfunction\n"
    "  function void inc_df(); df++; endfunction\n"
    "  function void inc_fp(); fp++; endfunction\n"
    "  function void inc_ff(); ff++; endfunction\n"
    "  function logic [7:0] id(logic [7:0] v); return v; endfunction\n";

std::vector<std::string> CounterNames() {
  return {"ap", "af", "dp", "df", "fp", "ff"};
}

TEST(CheckerEventControlReads,
     DISABLED_TheClausesResetExampleReadsTheCurrentReset) {
  EXPECT_EQ(Values("checker chk(logic b, logic clk, logic rst);\n"
                   "  logic z, w;\n"
                   "  always_ff @(posedge clk or negedge rst)\n"
                   "    if (rst) z <= b;\n"
                   "    else z <= 1'b0;\n"
                   "  always_ff @(posedge clk) if (clk) w <= 1'b1;\n"
                   "    else w <= 1'b0;\n"
                   "endchecker\n"
                   "module top;\n"
                   "  logic clk = 0, rst = 1, b = 1;\n"
                   "  chk c(b, clk, rst);\n"
                   "  initial begin\n"
                   "    #5 clk = 1;\n"
                   "    #5 rst = 0;\n"
                   "    #2 $finish;\n"
                   "  end\n"
                   "endmodule\n",
                   In("c", {"z", "w"})),
            (std::vector<uint64_t>{0, 1}));
}

TEST(CheckerEventControlReads,
     DISABLED_EachReadOfTheClockTakesItsCurrentValue) {
  std::vector<std::string> names = {"n", "cs", "ci", "fa", "ix"};
  for (const auto& name : CounterNames()) names.push_back(name);
  EXPECT_EQ(
      Values("checker chk(logic clk);\n" + std::string(kCounters) +
                 "  logic n = 0, cs = 0, ci = 0;\n"
                 "  logic [7:0] fa = 0;\n"
                 "  logic [1:0] ix = 0;\n"
                 "  always_ff @(posedge clk) n <= clk;\n"
                 "  always_ff @(posedge clk)\n"
                 "    case (clk) 1'b1: cs <= 1; default: cs <= 0; endcase\n"
                 "  always_ff @(posedge clk)\n"
                 "    case (1'b1) clk: ci <= 1; default: ci <= 0; endcase\n"
                 "  always_ff @(posedge clk) fa <= id(clk);\n"
                 "  always_ff @(posedge clk) ix[clk] <= 1'b1;\n"
                 "  always_ff @(posedge clk)\n"
                 "    a1: assert (clk) inc_ap(); else inc_af();\n"
                 "  always_ff @(posedge clk)\n"
                 "    a2: assert #0 (clk) inc_dp(); else inc_df();\n"
                 "  always_ff @(posedge clk)\n"
                 "    a3: assert final (clk) inc_fp(); else inc_ff();\n"
                 "endchecker\n"
                 "module top;\n"
                 "  logic clk = 0;\n"
                 "  chk c(clk);\n"
                 "  initial begin\n"
                 "    #5 clk = 1;\n"
                 "    #2 $finish;\n"
                 "  end\n"
                 "endmodule\n",
             In("c", names)),
      (std::vector<uint64_t>{1, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0}));
}

TEST(CheckerEventControlReads,
     DISABLED_ALevelOrGuardVariableTakesItsCurrentValue) {
  EXPECT_EQ(Values("checker chk(logic clk, logic rst, logic en, event e3);\n"
                   "  logic g = 1, ls = 1, h = 0;\n"
                   "  always_ff @(rst) g <= rst;\n"
                   "  always_ff @(rst or e3) ls <= rst;\n"
                   "  always_ff @(posedge clk iff en) h <= en;\n"
                   "endchecker\n"
                   "module top;\n"
                   "  logic clk = 0, rst = 1, en = 0;\n"
                   "  event e3;\n"
                   "  chk c(clk, rst, en, e3);\n"
                   "  initial begin\n"
                   "    #5 en = 1;\n"
                   "    clk = 1;\n"
                   "    #5 rst = 0;\n"
                   "    #2 $finish;\n"
                   "  end\n"
                   "endmodule\n",
                   In("c", {"g", "ls", "h"})),
            (std::vector<uint64_t>{0, 0, 1}));
}

TEST(CheckerEventControlReads,
     DISABLED_ACheckerVariableInTheEventControlIsCurrent) {
  EXPECT_EQ(Values("checker chk(logic clk);\n"
                   "  logic t = 0, u = 0;\n"
                   "  always_ff @(posedge clk) t <= 1'b1;\n"
                   "  always_ff @(posedge t) u <= t;\n"
                   "endchecker\n"
                   "module top;\n"
                   "  logic clk = 0;\n"
                   "  chk c(clk);\n"
                   "  initial begin\n"
                   "    #5 clk = 1;\n"
                   "    #2 $finish;\n"
                   "  end\n"
                   "endmodule\n",
                   In("c", {"u"})),
            (std::vector<uint64_t>{1}));
}

TEST(CheckerEventControlReads, DISABLED_AnEnclosingScopesVariableIsCurrent) {
  EXPECT_EQ(Values("module top;\n"
                   "  logic clk2 = 0;\n"
                   "  checker chk;\n"
                   "    logic k = 0;\n"
                   "    always_ff @(posedge clk2) k <= clk2;\n"
                   "  endchecker\n"
                   "  chk c();\n"
                   "  initial begin\n"
                   "    #5 clk2 = 1;\n"
                   "    #2 $finish;\n"
                   "  end\n"
                   "endmodule\n",
                   In("c", {"k"})),
            (std::vector<uint64_t>{1}));
}

std::string CheckerOverB(const std::string& body, int end) {
  return "checker chk(int b, logic clk);\n" + std::string(kCounters) + body +
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  int b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) b = b + 1;\n"
         "  chk c(b, clk);\n"
         "  initial #" +
         std::to_string(end) +
         " $finish;\n"
         "endmodule\n";
}

TEST(CheckerAlwaysFfSampling, EveryOtherExpressionReadsTheSampledValue) {
  std::vector<std::string> names = {"i1", "e1", "c1", "c2", "f1",
                                    "lb", "ix", "cr", "ffv"};
  for (const auto& name : CounterNames()) names.push_back(name);
  EXPECT_EQ(
      Values(CheckerOverB(
                 "  int i1 = 9, e1 = 9, c1 = 9, c2 = 9, cw, cr = 9, ffv = 9;\n"
                 "  logic [7:0] f1 = 0, lb = 0, ix = 0;\n"
                 "  always_comb cw = b;\n"
                 "  always_ff @(posedge clk) if (b == 2) i1 <= 1;\n"
                 "    else i1 <= 0;\n"
                 "  always_ff @(posedge clk) if (b == 7) e1 <= 0;\n"
                 "    else e1 <= b;\n"
                 "  always_ff @(posedge clk)\n"
                 "    case (b) 2: c1 <= 1; default: c1 <= 0; endcase\n"
                 "  always_ff @(posedge clk)\n"
                 "    case (2) b: c2 <= 1; default: c2 <= 0; endcase\n"
                 "  always_ff @(posedge clk) f1 <= id(b);\n"
                 "  always_ff @(posedge clk)\n"
                 "    for (int i = 0; i < b; i++) lb[i] <= 1'b1;\n"
                 "  always_ff @(posedge clk) ix[b] <= 1'b1;\n"
                 "  always_ff @(posedge clk) cr <= cw;\n"
                 "  always_ff @(posedge clk) ffv <= b;\n"
                 "  always_ff @(posedge clk)\n"
                 "    a1: assert (b % 2 == 0) inc_ap(); else inc_af();\n"
                 "  always_ff @(posedge clk)\n"
                 "    a2: assert #0 (b % 2 == 0) inc_dp(); else inc_df();\n"
                 "  always_ff @(posedge clk)\n"
                 "    a3: assert final (b % 2 == 0) inc_fp(); else inc_ff();\n",
                 27),
             In("c", names)),
      (std::vector<uint64_t>{1, 2, 1, 1, 2, 3, 7, 2, 2, 2, 1, 2, 1, 2, 1}));
}

TEST(CheckerCombAndLatchReads, EveryExpressionReadsTheCurrentValue) {
  EXPECT_EQ(
      Values(CheckerOverB("  int vn, l1, l2, ce, ci, cc, cl, ffv;\n"
                          "  logic [7:0] cf;\n"
                          "  bit lp;\n"
                          "  always_comb vn <= b;\n"
                          "  always_latch if (b > 0) l1 = b;\n"
                          "  always_latch if (b > 0) l2 <= b;\n"
                          "  always_latch if (b > 3) ce = 1; else ce = 0;\n"
                          "  always_comb if (b > 3) ci = 1; else ci = 0;\n"
                          "  always_comb case (b) 4: cc = 1; default: cc = 0; "
                          "endcase\n"
                          "  always_comb begin\n"
                          "    cl = 0;\n"
                          "    for (int i = 0; i < b; i++) cl = cl + 1;\n"
                          "  end\n"
                          "  always_comb cf = id(b);\n"
                          "  always_comb begin\n"
                          "    let p = b % 2 == 0;\n"
                          "    lp = p;\n"
                          "  end\n"
                          "  always_ff @(posedge clk) ffv <= b;\n",
                          42),
             In("c",
                {"vn", "l1", "l2", "ce", "ci", "cc", "cl", "cf", "lp", "ffv"})),
      (std::vector<uint64_t>{4, 4, 4, 1, 1, 1, 4, 4, 1, 3}));
}

TEST(CheckerCombAndLatchReads, EachAssertionReadsTheCurrentValue) {
  EXPECT_EQ(Values(CheckerOverB(
                       "  always_comb a2: assert (b % 2 == 0) inc_ap(); "
                       "else inc_af();\n"
                       "  always_latch if (b >= 0)\n"
                       "    a3: assert (b % 2 == 0) inc_dp(); else inc_df();\n",
                       42),
                   In("c", {"ap", "af", "dp", "df"})),
            (std::vector<uint64_t>{3, 2, 3, 2}));
}

TEST(CheckerCombAndLatchReads, EachDeferredAssertionReadsTheCurrentValue) {
  EXPECT_EQ(
      Values(CheckerOverB(
                 "  always_comb d2: assert #0 (b % 2 == 0) inc_ap(); "
                 "else inc_af();\n"
                 "  always_latch if (b >= 0)\n"
                 "    d3: assert #0 (b % 2 == 0) inc_dp(); else inc_df();\n",
                 42),
             In("c", {"ap", "af", "dp", "df"})),
      (std::vector<uint64_t>{3, 2, 3, 2}));
}

std::string WithCounters(const std::string& head, const std::string& body) {
  return head + kCounters + body + "endchecker\n";
}

TEST(CheckerProcedureAssertions, AnImmediateAssertionInCombRunsEachTime) {
  EXPECT_EQ(Values(CheckerOverB("  always_comb begin\n"
                                "    a1: assert (b != 0) inc_ap(); else "
                                "inc_af();\n"
                                "  end\n",
                                42),
                   In("c", {"ap", "af"})),
            (std::vector<uint64_t>{4, 1}));
}

TEST(CheckerProcedureAssertions, AnImmediateAssertionInALatchRunsWhileEnabled) {
  EXPECT_EQ(
      Values(WithCounters("checker chk(int b, logic en);\n",
                          "  int l;\n"
                          "  always_latch if (en) l = b;\n"
                          "  always_latch if (en) begin\n"
                          "    a1: assert (b != 2) inc_ap(); else inc_af();\n"
                          "  end\n") +
                 "module top;\n"
                 "  logic clk = 0, en = 1;\n"
                 "  int b = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  always @(posedge clk) b = b + 1;\n"
                 "  chk c(b, en);\n"
                 "  initial begin\n"
                 "    #20 en = 0;\n"
                 "    #22 $finish;\n"
                 "  end\n"
                 "endmodule\n",
             In("c", {"ap", "af", "l"})),
      (std::vector<uint64_t>{2, 1, 2}));
}

TEST(CheckerProcedureAssertions, AnInitialsImmediateAssertionRunsOnce) {
  EXPECT_EQ(Values(WithCounters("checker chk(logic ok);\n",
                                "  initial a0: assert (ok == 1'b0) inc_ap(); "
                                "else inc_af();\n") +
                       "module top;\n"
                       "  logic ok = 0;\n"
                       "  chk c(ok);\n"
                       "  initial #3 $finish;\n"
                       "endmodule\n",
                   In("c", {"ap", "af"})),
            (std::vector<uint64_t>{1, 0}));
}

TEST(CheckerProcedureAssertions,
     DISABLED_ACombDeferredAssertionReportsOnceSettled) {
  EXPECT_EQ(
      Values(WithCounters("checker chk(logic a, logic b);\n",
                          "  always_comb d1: assert #0 (a != b) inc_ap(); "
                          "else inc_af();\n"
                          "  always_comb a1: assert (a != b) inc_dp(); "
                          "else inc_df();\n") +
                 "program drv;\n"
                 "  initial begin\n"
                 "    #5 top.a = 1;\n"
                 "    #0 top.b = 0;\n"
                 "    #5 $finish;\n"
                 "  end\n"
                 "endprogram\n"
                 "module top;\n"
                 "  logic a = 0, b = 1;\n"
                 "  drv d();\n"
                 "  chk c(a, b);\n"
                 "endmodule\n",
             In("c", {"ap", "af", "dp", "df"})),
      (std::vector<uint64_t>{2, 0, 2, 1}));
}

const char* const kCountingFf =
    "  int n = 0;\n"
    "  always_ff @(posedge clk) begin\n"
    "    n <= n + 1;\n"
    "    a1: assert property (n < 3) inc_ap(); else inc_af();\n"
    "  end\n";

const char* const kClockedTop =
    "  logic clk = 0;\n"
    "  always #5 clk = ~clk;\n"
    "  initial #52 $finish;\n";

TEST(CheckerProceduralConcurrentRuns, DISABLED_AnEventFormalsActualClocksIt) {
  EXPECT_EQ(Values(WithCounters("checker c1(event clk);\n",
                                "  int n = 0;\n"
                                "  always_ff @(clk) begin\n"
                                "    n <= n + 1;\n"
                                "    p0: assert property (n < 3) inc_ap(); "
                                "else inc_af();\n"
                                "  end\n") +
                       "module top;\n" + kClockedTop +
                       "  event ev;\n"
                       "  always @(posedge clk) -> ev;\n"
                       "  c1 u(posedge clk);\n"
                       "  c1 w(ev);\n"
                       "endmodule\n",
                   {"top.u.ap", "top.u.af", "top.w.ap", "top.w.af"}),
            (std::vector<uint64_t>{3, 2, 3, 2}));
}

TEST(CheckerProceduralConcurrentRuns, EveryInstanceIsQueuedAtEveryEdge) {
  std::vector<std::string> names;
  for (const char* scope : {"top.s", "pi", "o.in", "top.i.c", "top.g[0].c"}) {
    for (const char* counter : {".ap", ".af"}) {
      std::string name = scope;
      name += counter;
      names.push_back(name);
    }
  }
  EXPECT_EQ(Values(WithCounters("checker c2(logic clk);\n", kCountingFf) +
                       "checker outer(logic clk);\n"
                       "  c2 in(clk);\n"
                       "endchecker\n"
                       "interface ifc(input logic clk);\n"
                       "  c2 c(clk);\n"
                       "endinterface\n"
                       "module top;\n" +
                       kClockedTop +
                       "  logic en = 1;\n"
                       "  initial #20 en = 0;\n"
                       "  c2 s(clk);\n"
                       "  always @(posedge clk) if (en) begin : pb\n"
                       "    c2 pi(clk);\n"
                       "  end\n"
                       "  initial @(posedge clk) begin : ob\n"
                       "    outer o(clk);\n"
                       "  end\n"
                       "  ifc i(clk);\n"
                       "  for (genvar k = 0; k < 1; k++) begin : g\n"
                       "    c2 c(clk);\n"
                       "  end\n"
                       "endmodule\n",
                   names),
            (std::vector<uint64_t>{3, 2, 3, 2, 3, 2, 3, 2, 3, 2}));
}

TEST(CheckerProceduralConcurrentRuns, AnInstanceInAProgramIsQueuedAtEveryEdge) {
  EXPECT_EQ(Values(WithCounters("checker c2(logic clk);\n", kCountingFf) +
                       "program prg(input logic clk);\n"
                       "  c2 c(clk);\n"
                       "endprogram\n"
                       "module top;\n" +
                       kClockedTop +
                       "  prg p(clk);\n"
                       "endmodule\n",
                   {"top.p.c.ap", "top.p.c.af"}),
            (std::vector<uint64_t>{3, 2}));
}

TEST(CheckerProceduralConcurrentRuns, AnOwnClockStartsEachAttemptAtItsTick) {
  EXPECT_EQ(Values(WithCounters("checker c3(logic clk, logic other);\n",
                                "  int n = 0;\n"
                                "  always_ff @(posedge clk) begin\n"
                                "    n <= n + 1;\n"
                                "    a1: assert property (@(posedge other) "
                                "n < 3) inc_ap(); else inc_af();\n"
                                "  end\n") +
                       "module top;\n" + kClockedTop +
                       "  logic other = 0;\n"
                       "  always #10 other = ~other;\n"
                       "  c3 c(clk, other);\n"
                       "endmodule\n",
                   In("c", {"ap", "af"})),
            (std::vector<uint64_t>{1, 4}));
}

TEST(CheckerProceduralConcurrentRuns, CombAndLatchTakeTheDefaultClocking) {
  EXPECT_EQ(
      Values(WithCounters("checker c4(logic clk, int d, logic en);\n",
                          "  default clocking @(posedge clk); endclocking\n"
                          "  always_comb a1: assert property (d < 2) "
                          "inc_ap(); else inc_af();\n"
                          "  always_latch if (en) a2: assert property (d < 2) "
                          "inc_dp(); else inc_df();\n") +
                 "module top;\n"
                 "  logic clk = 0, en = 1;\n"
                 "  int d = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  c4 c(clk, d, en);\n"
                 "  initial begin\n"
                 "    #2 d = 1;\n"
                 "    #10 d = 0;\n"
                 "    #10 d = 2;\n"
                 "    #10 $finish;\n"
                 "  end\n"
                 "endmodule\n",
             In("c", {"ap", "af", "dp", "df"})),
      (std::vector<uint64_t>{3, 1, 3, 1}));
}

TEST(CheckerProceduralConcurrentRuns, AnInitialsAssertionMakesOneAttempt) {
  EXPECT_EQ(Values(WithCounters("checker c5(logic clk, logic a);\n",
                                "  initial a1: assert property (@(posedge clk) "
                                "a) inc_ap(); else inc_af();\n") +
                       "module top;\n" + kClockedTop +
                       "  logic a = 0;\n"
                       "  c5 c(clk, a);\n"
                       "endmodule\n",
                   In("c", {"ap", "af"})),
            (std::vector<uint64_t>{0, 1}));
}

TEST(CheckerFinalRuns, EachStatementOfTheFinalRunsOncePerInstance) {
  EXPECT_EQ(
      SortedOutput(
          "checker chk(logic a);\n"
          "  function int twice(int v); return 2 * v; endfunction\n"
          "  final begin\n"
          "    if (a) $display(\"%m if\"); else $display(\"%m else\");\n"
          "    case (a) 1'b1: $display(\"%m one\"); "
          "default: $display(\"%m zero\"); endcase\n"
          "    for (int i = 0; i < 2; i++) $display(\"%m loop %0d\", i);\n"
          "    a1: assert (a) $display(\"%m pass\"); "
          "else $display(\"%m fail\");\n"
          "    $display(\"%m call %0d\", twice(3));\n"
          "  end\n"
          "endchecker\n"
          "module top;\n"
          "  logic a = 1, b = 0;\n"
          "  chk c1(a);\n"
          "  chk c2(b);\n"
          "  initial #1 $finish;\n"
          "endmodule\n"),
      (std::vector<std::string>{
          "top.c1 call 6", "top.c1 if", "top.c1 loop 0", "top.c1 loop 1",
          "top.c1 one", "top.c1.a1 pass", "top.c2 call 6", "top.c2 else",
          "top.c2 loop 0", "top.c2 loop 1", "top.c2 zero", "top.c2.a1 fail"}));
}

std::vector<std::string> BothFinals(const std::vector<std::string>& scopes) {
  std::vector<std::string> lines;
  for (const auto& scope : scopes) {
    for (const char* which : {" first", " second"}) {
      std::string line = scope;
      line += which;
      lines.push_back(line);
    }
  }
  std::sort(lines.begin(), lines.end());
  return lines;
}

const char* const kTwoFinals =
    "checker chk;\n"
    "  final $display(\"%m first\");\n"
    "  final $display(\"%m second\");\n"
    "endchecker\n";

TEST(CheckerFinalRuns, BothFinalsRunOnceInEveryStaticContext) {
  EXPECT_EQ(
      SortedOutput(std::string(kTwoFinals) +
                   "checker outer;\n"
                   "  chk c();\n"
                   "  if (1) begin : g\n"
                   "    chk c();\n"
                   "  end\n"
                   "endchecker\n"
                   "interface ifc;\n"
                   "  chk c();\n"
                   "endinterface\n"
                   "program prg;\n"
                   "  chk c();\n"
                   "endprogram\n"
                   "module top;\n"
                   "  chk c1();\n"
                   "  chk c2();\n"
                   "  ifc i();\n"
                   "  prg p();\n"
                   "  outer o();\n"
                   "  for (genvar k = 0; k < 2; k++) begin : g\n"
                   "    chk c();\n"
                   "  end\n"
                   "  if (1) begin : gi\n"
                   "    chk c();\n"
                   "  end\n"
                   "  initial #1 $finish;\n"
                   "endmodule\n"),
      BothFinals({"top.c1", "top.c2", "top.g[0].c", "top.g[1].c", "top.gi.c",
                  "top.i.c", "top.o.c", "top.o.g.c", "top.p.c"}));
}

const char* const kProceduralTop =
    "module top;\n"
    "  logic clk = 0, en = 0;\n"
    "  initial begin : ib\n"
    "    chk ci(1);\n"
    "  end\n"
    "  always @(posedge clk) if (en) begin : ab\n"
    "    chk ca(2);\n"
    "  end\n"
    "  always @(posedge clk) begin : ar\n"
    "    chk cr(3);\n"
    "  end\n"
    "  initial begin\n"
    "    #1 clk = 1;\n"
    "    #1 $finish;\n"
    "  end\n"
    "endmodule\n";

TEST(CheckerFinalRuns, AProceduralInstancesFinalRunsOnceReachedOrNot) {
  EXPECT_EQ(SortedOutput(std::string("checker chk(int id);\n"
                                     "  final $display(\"final %0d\", id);\n"
                                     "endchecker\n") +
                         kProceduralTop),
            (std::vector<std::string>{"final 1", "final 2", "final 3"}));
}

TEST(CheckerFinalRuns, DISABLED_AProceduralInstanceIsNamedThroughItsBlock) {
  EXPECT_EQ(SortedOutput(std::string("checker chk(int id);\n"
                                     "  final $display(\"%m\");\n"
                                     "endchecker\n") +
                         kProceduralTop),
            (std::vector<std::string>{"top.ab.ca", "top.ar.cr", "top.ib.ci"}));
}

}  // namespace
