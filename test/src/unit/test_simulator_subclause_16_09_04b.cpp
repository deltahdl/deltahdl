#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "helpers_assertion_run.h"
#include "helpers_placed_assertion_runs.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

void ExpectLines(const std::string& src, const std::string& want) {
  EXPECT_EQ(RunPlaced(src).lines, PlacedExpected(want, "")) << src;
}

std::string Repeated(const std::string& line, int times) {
  std::string out;
  for (int i = 0; i < times; ++i) out += line;
  return out;
}

constexpr const char* kFigureSignals =
    "  logic gclk = 0, clk = 1, sig = 1;\n"
    "  logic [1:0] v = 2'b01, w = 2'b01;\n"
    "  logic [4:0] e = 0;\n"
    "  logic [5:0] p = 0, q = 0;\n"
    "  initial begin #10; repeat (12) begin gclk = 1; #5 gclk = 0; #5; end "
    "end\n"
    "  global clocking @(posedge gclk); endclocking\n"
    "  initial begin\n"
    "    #10 clk = 0; sig = 0; v = 2'b11;\n"
    "    #20 clk = 1; v = 2'b10;\n"
    "    #20 clk = 0; sig = 1; v = 2'b11; w = 2'b11;\n"
    "    #20 clk = 1;\n"
    "    #10 sig = 0;\n"
    "    #10 clk = 0;\n"
    "    #20 clk = 1;\n"
    "  end\n"
    "  initial begin\n"
    "    #5 e = 5'b00101; q = 6'b010010;\n"
    "    #10 e = 5'b00010; p = 6'b010001;\n"
    "    #10 p = 6'b110010;\n"
    "    #10 p = 6'b110101;\n"
    "    #10 e = 5'b11001; p = 6'b100010; q = 6'b110001;\n"
    "    #10 e = 5'b10010; p = 6'b101001; q = 6'b110010;\n"
    "    #10 p = 6'b110010;\n"
    "    #10 e = 5'b00101;\n"
    "    #10 e = 5'b00010;\n"
    "  end\n";

constexpr PlacedDesign kFigure = {
    kFigureSignals,
    "(input logic gclk, clk, sig, input logic [1:0] v, w,"
    " input logic [4:0] e, input logic [5:0] p, q)",
    "gclk, clk, sig, v, w, e, p, q"};

constexpr const char* kFigurePlaces[] = {"module", "interface", "program"};

std::string OnGclk(std::string items) {
  const std::string kFrom = "$global_clock";
  for (size_t at = items.find(kFrom); at != std::string::npos;
       at = items.find(kFrom, at)) {
    items.replace(at, kFrom.size(), "posedge gclk");
  }
  return items;
}

void ExpectFigureLines(const std::string& items, const std::string& want) {
  for (const char* place : kFigurePlaces) {
    SCOPED_TRACE(place);
    ExpectLines(PlacedSource(kFigure, place, items), want);
  }
}

void ExpectFigureLinesInAGenerateBlockAndAChecker(const std::string& items,
                                                  const std::string& want) {
  SCOPED_TRACE("generate");
  ExpectLines(PlacedSource(kFigure, "generate", OnGclk(items)), want);
  SCOPED_TRACE("checker");
  ExpectLines(PlacedSource(kFigure, "checker", items), want);
}

std::string Checked(const std::string& name, const std::string& condition) {
  return "assert property (@($global_clock) " + condition + ") $display(\"" +
         name + " ok\"); else $display(\"" + name +
         " mismatch %0t\", $time);\n";
}

TEST(GlobalClockingValueRun, TheFutureFunctionsGiveTheClausesTable) {
  ExpectFigureLines(Checked("future",
                            "{$future_gclk(sig), $rising_gclk(sig), "
                            "$falling_gclk(sig), $steady_gclk(sig), "
                            "$changing_gclk(sig)} === e"),
                    Repeated("future ok\n", 11));
}

TEST(GlobalClockingValueRun, RisingAndFallingReadTheLsbAndSteadyTheWhole) {
  ExpectFigureLines(
      Checked("wide",
              "{$future_gclk(w), $rising_gclk(w), $falling_gclk(w), "
              "$steady_gclk(w), $changing_gclk(w)} === q"),
      Repeated("wide ok\n", 11));
}

TEST(GlobalClockingValueRun,
     DISABLED_EachFutureFunctionInAGenerateBlockOrAChecker) {
  ExpectFigureLinesInAGenerateBlockAndAChecker(
      Checked("future",
              "{$future_gclk(sig), $rising_gclk(sig), "
              "$falling_gclk(sig), $steady_gclk(sig), "
              "$changing_gclk(sig)} === e") +
          Checked("wide",
                  "{$future_gclk(w), $rising_gclk(w), "
                  "$falling_gclk(w), $steady_gclk(w), "
                  "$changing_gclk(w)} === q"),
      Repeated("future ok\n", 11) + Repeated("wide ok\n", 11));
}

constexpr const char* kPastFlags =
    "{$past_gclk(v), $rose_gclk(v), $fell_gclk(v), $stable_gclk(v), "
    "$changed_gclk(v)}";

constexpr const char* kCounterparts =
    "{$past(v, 1, 1, @(posedge gclk)), $rose(v, @(posedge gclk)), "
    "$fell(v, @(posedge gclk)), $stable(v, @(posedge gclk)), "
    "$changed(v, @(posedge gclk))}";

std::string PastChecks() {
  return Checked("same", std::string(kPastFlags) + " === " + kCounterparts) +
         Checked("past", "##1 (" + std::string(kPastFlags) + " === p)");
}

std::string PastLines() {
  return Repeated("same ok\n", 12) + Repeated("past ok\n", 11);
}

std::string Procedural(const std::string& place) {
  return (place == "program" ? "initial forever @($global_clock)"
                             : "always @($global_clock)") +
         std::string(" if ($time > 10)\n  if (") + kPastFlags +
         " === p) $display(\"proc ok\");\n"
         "  else $display(\"proc mismatch %0t\", $time);\n";
}

TEST(GlobalClockingValueRun, EachPastFunctionIsItsCounterpartOnTheGlobalClock) {
  ExpectLines(PlacedSource(kFigure, "module", PastChecks()), PastLines());
}

TEST(GlobalClockingValueRun, APastFunctionInProceduralCode) {
  ExpectLines(PlacedSource(kFigure, "module", Procedural("module")),
              Repeated("proc ok\n", 11));
}

TEST(GlobalClockingValueRun,
     DISABLED_ThePastFunctionsOfAPortInEachDesignElement) {
  for (const char* place : {"interface", "program", "checker"}) {
    SCOPED_TRACE(place);
    ExpectLines(PlacedSource(kFigure, place, PastChecks()), PastLines());
  }
  for (const char* place : {"interface", "program"}) {
    SCOPED_TRACE(place);
    ExpectLines(PlacedSource(kFigure, place, Procedural(place)),
                Repeated("proc ok\n", 11));
  }
}

TEST(GlobalClockingValueRun, ThePastFunctionsInAGenerateBlock) {
  ExpectLines(PlacedSource(kFigure, "generate", OnGclk(PastChecks())),
              PastLines());
}

constexpr const char* kExampleOne =
    "$changing_gclk(sig) |-> $falling_gclk(clk)";

TEST(GlobalClockingActionRun, TheClausesFirstExampleActsAtTheFollowingTick) {
  ExpectFigureLines(std::string("a1: assert property (@($global_clock) ") +
                        kExampleOne +
                        ")\n  $display(\"pass %0t\", $time);\n"
                        "  else $display(\"fail %0t\", $time);\n",
                    "pass 20\npass 30\npass 40\npass 50\npass 60\npass 70\n"
                    "pass 80\nfail 90\npass 100\npass 110\npass 120\n");
}

TEST(GlobalClockingActionRun, AssumeAndCoverActAtTheFollowingTick) {
  ExpectFigureLines(
      std::string("u1: assume property (@($global_clock) ") + kExampleOne +
          ") else $display(\"assume %0t\", $time);\n"
          "c1: cover property (@($global_clock) $changing_gclk(sig) ##0 "
          "!$falling_gclk(clk)) $display(\"cover %0t\", $time);\n"
          "c2: cover sequence (@($global_clock) $changing_gclk(sig) ##0 "
          "!$falling_gclk(clk)) $display(\"sequence %0t\", $time);\n",
      "assume 90\ncover 90\nsequence 90\n");
}

int ErrorLines(const std::string& lines) {
  int count = 0;
  for (const std::string& line : PlacedLines(lines)) {
    if (line.find("ERROR") != std::string::npos) ++count;
  }
  return count;
}

TEST(GlobalClockingActionRun, TheDefaultErrorWaitsForTheFollowingTick) {
  for (const char* place : kFigurePlaces) {
    SCOPED_TRACE(place);
    const std::string kItems =
        std::string("a1: assert property (@($global_clock) ") + kExampleOne +
        ");\n";
    EXPECT_EQ(ErrorLines(RunPlaced(PlacedSource(kFigure, place, kItems, "",
                                                "#85 $finish;"))
                             .lines),
              0);
    EXPECT_EQ(ErrorLines(RunPlaced(PlacedSource(kFigure, place, kItems, "",
                                                "#95 $finish;"))
                             .lines),
              1);
  }
}

TEST(GlobalClockingActionRun, DISABLED_TheClausesThirdExampleIsNotDisabled) {
  const std::string kItems =
      std::string("a3: assert property (@($global_clock) disable iff (rst) ") +
      kExampleOne + ") else $display(\"fail %0t\", $time);\n";
  const std::string kRst = "logic rst = 0;\n";
  for (const char* place : {"module"}) {
    SCOPED_TRACE(place);
    ExpectLines(
        PlacedSource(kFigure, place, kItems, kRst, "#82 rst = 1; #2 rst = 0;"),
        "fail 90\n");
    ExpectLines(
        PlacedSource(kFigure, place, kItems, kRst, "#88 rst = 1; #4 rst = 0;"),
        "fail 90\n");
    ExpectLines(
        PlacedSource(kFigure, place, kItems, kRst, "#78 rst = 1; #4 rst = 0;"),
        "");
  }
}

struct Clocking {
  const char* signals;
  const char* clock;
  int gap;
  int last_global_tick;
};

constexpr Clocking kClockings[] = {
    {"  logic clk = 0, a = 1, b = 0, c = 0, rst = 0;\n"
     "  initial repeat (20) #5 clk = ~clk;\n"
     "  global clocking @(posedge clk); endclocking\n",
     "@(posedge clk)", 10, 95},
    {"  logic clk = 0, a = 1, b = 0, c = 0, rst = 0;\n"
     "  initial repeat (20) #5 clk = ~clk;\n"
     "  global clocking @(posedge clk); endclocking\n",
     "@($global_clock)", 10, 95},
    {"  logic clk = 0, gclk = 0, a = 1, b = 0, c = 0, rst = 0;\n"
     "  initial repeat (20) #5 clk = ~clk;\n"
     "  initial begin #5; repeat (20) begin gclk = 1; #2 gclk = 0; #3; end "
     "end\n"
     "  global clocking @(posedge gclk); endclocking\n",
     "@(posedge clk)", 5, 100},
};

constexpr const char* kAttemptPlaces[] = {"module", "interface", "program",
                                          "checker"};

constexpr const char* kKinds[] = {"assert", "assume", "cover"};

struct AttemptCase {
  bool multi;
  const char* disable;
  const char* controls;
  std::vector<int> lost;
};

std::string AttemptItem(const char* kind, const AttemptCase& c,
                        const char* clock) {
  const bool kCover = std::string(kind) == "cover";
  std::string prop = c.multi ? "a ##1 1 |-> " : "";
  if (kCover) {
    prop += c.multi ? "$steady_gclk(c)" : "$steady_gclk(b)";
  } else {
    prop += c.multi ? "$falling_gclk(c)" : "$rising_gclk(b)";
  }
  return std::string("a1: ") + kind + " property (" + clock + " " + c.disable +
         prop + ")" + (kCover ? " " : " else ") +
         "$display(\"fail %0t\", $time);\n";
}

std::string Verdicts(const AttemptCase& c, const Clocking& clocking) {
  std::string out;
  for (int start = 5; start <= 95; start += 10) {
    bool lost = false;
    for (int t : c.lost) lost = lost || t == start;
    const int kVerdict = start + (c.multi ? 10 : 0) + clocking.gap;
    if (!lost && kVerdict <= clocking.last_global_tick) {
      out += "fail " + std::to_string(kVerdict) + "\n";
    }
  }
  return out;
}

std::string Scoped(std::string text, const std::string& scope) {
  for (size_t at = text.find('%'); at != std::string::npos;
       at = text.find('%', at + scope.size())) {
    text.replace(at, 1, scope);
  }
  return text;
}

void ExpectAttempts(const AttemptCase& c,
                    const std::string& declarations = "") {
  for (const Clocking& clocking : kClockings) {
    const PlacedDesign kDesign = {clocking.signals,
                                  "(input logic clk, a, b, c, rst)",
                                  "clk, a, b, c, rst"};
    for (const char* kind : kKinds) {
      for (const char* place : kAttemptPlaces) {
        SCOPED_TRACE(std::string(place) + " " + kind + " " + clocking.clock);
        ExpectLines(
            PlacedSource(kDesign, place, AttemptItem(kind, c, clocking.clock),
                         declarations, Scoped(c.controls, PlacedScope(place))),
            Verdicts(c, clocking));
      }
    }
  }
}

TEST(GlobalClockingActionRun,
     DISABLED_AProcedureOrGenerateBlocksAssertionWaits) {
  const AttemptCase kNoControl = {false, "", "", {}};
  const PlacedDesign kDesign = {kClockings[0].signals,
                                "(input logic clk, a, b, c, rst)",
                                "clk, a, b, c, rst"};
  for (const char* place : {"always", "generate"}) {
    SCOPED_TRACE(place);
    ExpectLines(
        PlacedSource(kDesign, place,
                     AttemptItem("assert", kNoControl, "@(posedge clk)")),
        Verdicts(kNoControl, kClockings[0]));
  }
}

TEST(FutureAttemptKillRun, DISABLED_AKillAfterAOneTickAttemptLeavesIt) {
  for (const char* kill :
       {"$assertcontrol(5);", "$assertkill;", "$assertkill(0, %.a1);"}) {
    ExpectAttempts({false,
                    "",
                    (std::string("#7 ") + kill + " #5 $asserton;").c_str(),
                    {}});
  }
}

TEST(FutureAttemptKillRun, DISABLED_AKillAtTheNextGlobalTickLeavesTheAttempt) {
  ExpectAttempts({false, "", "#15 $assertkill; #2 $asserton;", {15}});
}

TEST(FutureAttemptKillRun, DISABLED_AKillAtTheAttemptsOwnTickAbortsIt) {
  ExpectAttempts({false, "", "#5 $assertkill; #2 $asserton;", {5}});
}

TEST(FutureAttemptKillRun, DISABLED_AKillInsideAMultiTickAttemptAbortsIt) {
  ExpectAttempts({true, "", "#7 $assertkill; #5 $asserton;", {5}});
  ExpectAttempts({true, "", "#7 $assertcontrol(5); #5 $asserton;", {5}});
}

TEST(FutureAttemptKillRun, DISABLED_AKillAtAMultiTickAttemptsLastTickAbortsIt) {
  ExpectAttempts({true, "", "#15 $assertkill; #7 $asserton;", {5, 15}});
}

TEST(FutureAttemptKillRun,
     DISABLED_AKillAfterAMultiTickAttemptsLastTickLeavesIt) {
  ExpectAttempts({true, "", "#17 $assertkill; #5 $asserton;", {15}});
}

constexpr const char* kWritten = "disable iff (rst) ";

const std::vector<AttemptCase>& DisableCases(const char* disable) {
  static std::vector<AttemptCase> written;
  static std::vector<AttemptCase> defaulted;
  std::vector<AttemptCase>& cases = *disable == '\0' ? defaulted : written;
  if (cases.empty()) {
    cases = {{false, disable, "#4 rst = 1; #2 rst = 0;", {5}},
             {false, disable, "#5 rst = 1; #1 rst = 0;", {5}},
             {false, disable, "#14 rst = 1; #2 rst = 0;", {15}},
             {false, disable, "#7 rst = 1; #2 rst = 0;", {}},
             {true, disable, "#14 rst = 1; #2 rst = 0;", {5, 15}}};
  }
  return cases;
}

TEST(FutureAttemptDisableRun, DISABLED_AConditionAtTheAttemptsTickDisablesIt) {
  ExpectAttempts(DisableCases(kWritten)[0]);
  ExpectAttempts(DisableCases(kWritten)[1]);
}

TEST(FutureAttemptDisableRun,
     DISABLED_AConditionOnlyAtTheNextGlobalTickLeavesIt) {
  ExpectAttempts(DisableCases(kWritten)[2]);
}

TEST(FutureAttemptDisableRun, AConditionAfterTheLastTickLeavesTheAttempt) {
  ExpectAttempts(DisableCases(kWritten)[3]);
}

TEST(FutureAttemptDisableRun,
     DISABLED_AConditionAtAMultiTickAttemptsLastTickDisables) {
  ExpectAttempts(DisableCases(kWritten)[4]);
}

TEST(FutureAttemptDisableRun, DISABLED_EachConditionFromADefaultDisableIff) {
  for (const AttemptCase& c : DisableCases("")) {
    ExpectAttempts(c, "default disable iff rst;\n");
  }
}

class FutureAttemptVpiKill : public AssertionRun {};

std::string VpiDesign(const char* prop) {
  return std::string(
             "module top;\n"
             "  logic clk = 0, a = 1, b = 0, c = 0;\n"
             "  int f = 0, first = 0;\n"
             "  initial repeat (20) #5 clk = ~clk;\n"
             "  global clocking @(posedge clk); endclocking\n"
             "  a1: assert property (@(posedge clk) ") +
         prop +
         ")\n"
         "    else begin if (f == 0) first = $time; f++; end\n"
         "  initial begin #7 $arm; #5 $arm; end\n"
         "endmodule\n";
}

void KillAttemptAtFive() {
  s_vpi_time start = {};
  start.type = vpiSimTime;
  start.low = 5;
  vpi_control(vpiAssertionKill, vpi_handle_by_name(VpiText("top.a1"), nullptr),
              &start);
}

TEST_F(FutureAttemptVpiKill, AnAttemptKillAfterAOneTickAttemptLeavesIt) {
  ArmInTurn({KillAttemptAtFive, [] {}});
  Run(VpiDesign("$rising_gclk(b)"));
  EXPECT_EQ(IntOf("top.f"), 9);
  EXPECT_EQ(IntOf("top.first"), 15);
}

TEST_F(FutureAttemptVpiKill,
       DISABLED_AnAttemptKillInsideAMultiTickAttemptAbortsIt) {
  ArmInTurn({KillAttemptAtFive, [] {}});
  Run(VpiDesign("a ##1 1 |-> $falling_gclk(c)"));
  EXPECT_EQ(IntOf("top.f"), 7);
  EXPECT_EQ(IntOf("top.first"), 35);
}

void SysKill() { vpi_control(vpiAssertionSysKill, nullptr); }

void SysOn() { vpi_control(vpiAssertionSysOn, nullptr); }

TEST_F(FutureAttemptVpiKill, DISABLED_ASystemKillAfterAOneTickAttemptLeavesIt) {
  ArmInTurn({SysKill, SysOn});
  Run(VpiDesign("$rising_gclk(b)"));
  EXPECT_EQ(IntOf("top.f"), 9);
  EXPECT_EQ(IntOf("top.first"), 15);
}

TEST_F(FutureAttemptVpiKill,
       DISABLED_ASystemKillInsideAMultiTickAttemptAbortsIt) {
  ArmInTurn({SysKill, SysOn});
  Run(VpiDesign("a ##1 1 |-> $falling_gclk(c)"));
  EXPECT_EQ(IntOf("top.f"), 7);
  EXPECT_EQ(IntOf("top.first"), 35);
}

struct CheckerPast {
  const char* actual;
  int offset;
  int delay;
  bool global_in_checker;
  bool in_module;
};

std::string PastChecks(const std::string& x, int delay) {
  const std::string kDelay = "##" + std::to_string(delay) + " ";
  return "  assert property (@($global_clock) " + kDelay + "($past_gclk(" + x +
         ") === ep))\n"
         "    $display(\"past ok %0t\", $time);\n"
         "    else $display(\"past mismatch %0t\", $time);\n"
         "  assert property (@($global_clock) " +
         kDelay + "({$rose_gclk(" + x + "), $fell_gclk(" + x +
         "), $stable_gclk(" + x + "), $changed_gclk(" + x +
         ")} === ef))\n"
         "    $display(\"flags ok %0t\", $time);\n"
         "    else $display(\"flags mismatch %0t\", $time);\n";
}

std::string CheckerPastSource(const CheckerPast& c) {
  const std::string kGlobal = "  global clocking @(posedge clk); endclocking\n";
  const std::string kOffset = std::to_string(c.offset);
  std::string src;
  if (!c.in_module) {
    src =
        "checker chk(logic clk, logic [3:0] x, logic [3:0] ep, "
        "logic [3:0] ef);\n";
    if (c.global_in_checker) src += kGlobal;
    src += PastChecks("x", c.delay) + "endchecker\n";
  }
  src +=
      "module top;\n  logic clk = 0;\n  logic [3:0] cnt = 0, ep = 0, ef = 0;\n";
  src += "  wire [3:0] w = cnt;\n";
  if (!c.global_in_checker) src += kGlobal;
  src +=
      "  always #5 clk = ~clk;\n"
      "  always @(negedge clk) begin\n"
      "    cnt = cnt + 1;\n"
      "    ep = cnt - 1 + " +
      kOffset +
      ";\n"
      "    ef = ((cnt + " +
      kOffset +
      ") & 1) ? 4'b1001 : 4'b0101;\n"
      "  end\n";
  src += c.in_module ? PastChecks(c.actual, c.delay)
                     : "  chk k(clk, " + std::string(c.actual) + ", ep, ef);\n";
  return src + "  initial #50 $finish;\nendmodule\n";
}

std::string PastVerdicts(int delay) {
  std::string out;
  for (int t = 5 + 10 * delay; t <= 45; t += 10) {
    out += "past ok " + std::to_string(t) + "\nflags ok " + std::to_string(t) +
           "\n";
  }
  return out;
}

void ExpectCheckerPast(const CheckerPast& c) {
  ExpectLines(CheckerPastSource(c), PastVerdicts(c.delay));
}

TEST(CheckerGclkPastRun, DISABLED_AFormalBoundToAVariableFromTheSecondTick) {
  ExpectCheckerPast({"cnt", 0, 1, false, false});
}

TEST(CheckerGclkPastRun, DISABLED_TheFirstEvaluationStartedTwoTicksLate) {
  ExpectCheckerPast({"cnt", 0, 2, false, false});
}

TEST(CheckerGclkPastRun, DISABLED_AFormalBoundToAnExpressionOrANet) {
  ExpectCheckerPast({"cnt + 4'd1", 1, 1, false, false});
  ExpectCheckerPast({"w", 0, 1, false, false});
}

TEST(CheckerGclkPastRun, DISABLED_AGlobalClockingDeclaredInTheChecker) {
  ExpectCheckerPast({"cnt", 0, 1, true, false});
}

TEST(CheckerGclkPastRun, TheSameAssertionsWrittenInTheModule) {
  ExpectCheckerPast({"cnt", 0, 1, false, true});
  ExpectCheckerPast({"cnt + 4'd1", 1, 1, false, true});
}

TEST(CheckerGclkPastRun, DISABLED_AModuleEvaluationStartedTwoTicksLate) {
  ExpectCheckerPast({"cnt", 0, 2, false, true});
  ExpectCheckerPast({"cnt + 4'd1", 1, 2, false, true});
}

TEST(CheckerGclkPastRun, DISABLED_ANetWrittenInTheModule) {
  for (int delay : {1, 2}) {
    ExpectCheckerPast({"w", 0, delay, false, true});
  }
}

}  // namespace
