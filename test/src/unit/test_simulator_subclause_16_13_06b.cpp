#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

const char* const kInferenceSignals =
    "  logic clk_a = 0, clk_d = 0, clk_e = 0, a = 1, b = 0, c = 0;\n"
    "  always #5 clk_a = ~clk_a;\n"
    "  initial begin #8; forever begin clk_d = 1; #2 clk_d = 0; #18; end end\n"
    "  initial begin #3; forever begin clk_e = 1; #2 clk_e = 0; #18; end end\n"
    "  initial begin #12 b = 1; #18 b = 0; end\n"
    "  initial begin #20 c = 1; #10 c = 0; #10 c = 1; #10 c = 0; end\n"
    "  initial #70 $finish;\n";

const char* const kClocklessE4 = "  sequence e4; b ##1 c; endsequence\n";

const char* const kInferredFormalE4 =
    "  sequence e4(event ck = $inferred_clock); @(ck) b ##1 c; endsequence\n";

struct InferenceCase {
  const char* items;
  const char* after;
  const char* expected;
};

void ExpectEnds(const char* sequence, const InferenceCase& run) {
  std::string src = std::string(run.after) + "module t;\n" + kInferenceSignals +
                    sequence + run.items + "endmodule\n";
  EXPECT_EQ(PlacedSortedVerdicts(RunPlaced(src).lines), run.expected) << src;
}

const char* const kDefaultOnD =
    "  default clocking cb @(posedge clk_d); endclocking\n";

const char* const kWaitE4 =
    "  initial forever begin wait (e4.triggered); $display(\"w %0t\", $time);"
    " #1; end\n";

const char* const kProgramOnA =
    "  program p;\n"
    "    initial forever @(posedge clk_a)\n"
    "      if (e4.triggered) $display(\"p %0t\", $time);\n"
    "  endprogram\n"
    "  p u_p();\n";

std::string AssertionNoClock() {
  return std::string(kDefaultOnD) +
         "  c1: cover property (a && e4.triggered) $display(\"c %0t\", "
         "$time);\n";
}

std::string AssertionNoClockWhole() {
  return std::string(kDefaultOnD) +
         "  c1: cover property (e4.triggered) $display(\"c %0t\", $time);\n";
}

std::string ProgramProcedure() {
  return std::string(kDefaultOnD) + kProgramOnA;
}

std::string CheckerProcedure() {
  return "  checker chk(logic ca, logic cd);\n"
         "    default clocking cbc @(posedge cd); endclocking\n"
         "    always_ff @(posedge ca) if (e4.triggered) $display(\"k %0t\", "
         "$time);\n"
         "  endchecker\n"
         "  chk u_k(clk_a, clk_d);\n";
}

std::string ActionBlock() {
  return std::string(kDefaultOnD) +
         "  a1: assert property (@(posedge clk_a) a) begin\n"
         "    if (e4.triggered) $display(\"ab %0t\", $time);\n"
         "  end\n";
}

std::string ProgramDefault() {
  return "  default clocking cb @(posedge clk_a); endclocking\n"
         "  program p;\n"
         "    default clocking cbp @(posedge clk_d); endclocking\n" +
         std::string(kWaitE4) +
         "  endprogram\n"
         "  p u_p();\n";
}

std::string InterfaceDefault() {
  return "  default clocking cb @(posedge clk_a); endclocking\n"
         "  ifc u_i(clk_d, b, c);\n";
}

std::string InterfaceDeclaration() {
  return std::string(
      "interface ifc(input logic clk_d, b, c);\n"
      "  default clocking cbi @(posedge clk_d); endclocking\n"
      "%SEQUENCE%"
      "  initial forever begin wait (e4.triggered); $display(\"i %0t\", $time);"
      " #1; end\n"
      "endinterface\n");
}

std::string CheckerDefault() {
  return "  default clocking cb @(posedge clk_a); endclocking\n"
         "  checker chk(logic ca, logic cd);\n"
         "    default clocking cbc @(posedge cd); endclocking\n"
         "    always_ff @(posedge ca or posedge cd)\n"
         "      if (e4.triggered) $display(\"k %0t\", $time);\n"
         "    c1: cover property (a && e4.triggered) $display(\"c %0t\", "
         "$time);\n"
         "  endchecker\n"
         "  chk u_k(clk_a, clk_d);\n";
}

std::string AssertionAndWait() {
  return std::string(kDefaultOnD) +
         "  c1: cover property (@(posedge clk_a) e4.triggered) $display(\"c "
         "%0t\", "
         "$time);\n" +
         kWaitE4;
}

std::string ProcedureAndWait() { return ProgramProcedure() + kWaitE4; }

const char* const kInClockedSequence =
    "  sequence e5; @(posedge clk_e) e4.triggered; endsequence\n"
    "  c1: cover property (e5) $display(\"e5 %0t\", $time);\n";

const char* const kMatchedFromClockedSequence =
    "  sequence e5; @(posedge clk_e) e4.triggered; endsequence\n"
    "  c1: cover property (@(posedge clk_a) e5.matched) $display(\"m %0t\", "
    "$time);\n";

const char* const kInClocklessSequence =
    "  sequence e7; a ##0 e4.triggered; endsequence\n"
    "  c1: cover property (@(posedge clk_e) e7.triggered) $display(\"e7 "
    "%0t\", $time);\n";

const char* const kActualOfAnotherClock =
    "  sequence e6(f); @(posedge clk_e) f; endsequence\n"
    "  c1: cover property (@(posedge clk_a) a ##1 e6(e4.triggered))\n"
    "    $display(\"e6 %0t\", $time);\n";

std::string EventControlAmongSeveral() {
  return std::string(kDefaultOnD) +
         "  always @(posedge clk_a) begin @(e4); $display(\"ev %0t\", $time); "
         "end\n";
}

std::string WaitAmongSeveral() {
  return std::string(kDefaultOnD) +
         "  always @(posedge clk_a) begin\n"
         "    wait (e4.triggered); $display(\"w %0t\", $time); @(posedge "
         "clk_d);\n"
         "  end\n";
}

std::string BooleanAfterWait() {
  return std::string(kDefaultOnD) +
         "  initial begin\n"
         "    wait (e4.triggered);\n"
         "    if (e4.triggered) $display(\"r %0t\", $time);\n"
         "  end\n";
}

std::string EventControlInInitial() {
  return std::string(kDefaultOnD) +
         "  initial forever begin @(e4); $display(\"ev %0t\", $time); end\n";
}

std::string AssertionOnA() {
  return std::string(kDefaultOnD) +
         "  c1: cover property (@(posedge clk_a) e4.triggered) $display(\"c "
         "%0t\", "
         "$time);\n";
}

std::string SequenceBodyOnA() {
  return std::string(kDefaultOnD) +
         "  sequence s2; @(posedge clk_a) a ##0 e4.triggered; endsequence\n"
         "  c1: cover property (s2) $display(\"s2 %0t\", $time);\n";
}

std::string GenerateWait() {
  return std::string(kDefaultOnD) +
         "  if (1) begin : g\n"
         "    initial forever begin wait (e4.triggered); $display(\"g %0t\", "
         "$time); #1; end\n"
         "  end\n";
}

std::string WithSequence(const std::string& text, const char* sequence) {
  std::string out = text;
  size_t at = out.find("%SEQUENCE%");
  if (at != std::string::npos) out.replace(at, 10, sequence);
  return out;
}

void ExpectEndsIn(const char* sequence, const std::string& items,
                  const std::string& after, const char* expected) {
  ExpectEnds(sequence,
             {items.c_str(), WithSequence(after, sequence).c_str(), expected});
}

std::string WithLocalSequence(const std::string& checker) {
  std::string out = checker;
  out.insert(out.find('\n', out.find("checker chk(")) + 1,
             "    sequence e4; b ##1 c; endsequence\n");
  return out;
}

TEST(MethodClockInferenceRun, ACheckerProcedureTakesItsInferredClock) {
  ExpectEndsIn("", WithLocalSequence(CheckerProcedure()), "", "k 25\n");
}

TEST(MethodClockInferenceRun, ACheckerTakesItsOwnDefaultClocking) {
  ExpectEndsIn("", WithLocalSequence(CheckerDefault()), "", "c 48\nk 48\n");
}

TEST(MethodClockInferenceRun, AnAssertionWritingNoClockTakesTheDefault) {
  ExpectEndsIn(kClocklessE4, AssertionNoClock(), "", "c 48\n");
}

TEST(MethodClockInferenceRun,
     DISABLED_AWholeAssertionWritingNoClockTakesTheDefault) {
  ExpectEndsIn(kClocklessE4, AssertionNoClockWhole(), "", "c 48\n");
}

TEST(MethodClockInferenceRun, DISABLED_AProgramProcedureTakesItsInferredClock) {
  ExpectEndsIn(kClocklessE4, ProgramProcedure(), "", "p 25\n");
}

TEST(MethodClockInferenceRun,
     DISABLED_AModuleSequenceInACheckerProcedureTakesItsClock) {
  ExpectEndsIn(kClocklessE4, CheckerProcedure(), "", "k 25\n");
}

TEST(MethodClockInferenceRun,
     DISABLED_AProcedureInANestedProgramWithNoDefaultTakesItsClock) {
  ExpectEndsIn(kClocklessE4, kProgramOnA, "", "p 25\n");
}

TEST(MethodClockInferenceRun, DISABLED_AnActionBlockTakesTheLeadingClock) {
  ExpectEndsIn(kClocklessE4, ActionBlock(), "", "ab 25\n");
}

TEST(MethodClockInferenceRun, DISABLED_AProgramTakesItsOwnDefaultClocking) {
  ExpectEndsIn(kClocklessE4, ProgramDefault(), "", "w 48\n");
}

TEST(MethodClockInferenceRun, AnInterfaceTakesItsOwnDefaultClocking) {
  ExpectEndsIn(kClocklessE4, InterfaceDefault(), InterfaceDeclaration(),
               "i 48\n");
}

TEST(MethodClockInferenceRun,
     DISABLED_AModuleSequenceInACheckerTakesItsDefault) {
  ExpectEndsIn(kClocklessE4, CheckerDefault(), "", "c 48\nk 48\n");
}

TEST(MethodClockInferenceRun,
     DISABLED_AnAssertionAndAWaitEachTakeTheirOwnClock) {
  ExpectEndsIn(kClocklessE4, AssertionAndWait(), "", "c 25\nw 48\n");
}

TEST(MethodClockInferenceRun,
     DISABLED_AProcedureAndAWaitEachTakeTheirOwnClock) {
  ExpectEndsIn(kClocklessE4, ProcedureAndWait(), "", "p 25\nw 48\n");
}

TEST(MethodClockInferenceRun, ANestedUseTakesItsClockedSequencesClock) {
  ExpectEndsIn(kClocklessE4, kInClockedSequence, "", "e5 43\n");
}

TEST(MethodClockInferenceRun, MatchedReadsAClockedSequenceThatNestsIt) {
  ExpectEndsIn(kClocklessE4, kMatchedFromClockedSequence, "", "m 45\n");
}

TEST(MethodClockInferenceRun, ANestedUseTakesTheClockItsSequenceInfers) {
  ExpectEndsIn(kClocklessE4, kInClocklessSequence, "", "e7 43\n");
}

TEST(MethodClockInferenceRun,
     DISABLED_AnActualTakesTheClockOfItsFormalsSequence) {
  ExpectEndsIn(kClocklessE4, kActualOfAnotherClock, "", "e6 43\ne6 43\n");
}

TEST(MethodClockInferenceRun, AnEventControlAmongSeveralTakesTheDefault) {
  ExpectEndsIn(kClocklessE4, EventControlAmongSeveral(), "", "ev 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AWaitTakesTheDefaultClocking) {
  ExpectEndsIn(kInferredFormalE4, std::string(kDefaultOnD) + kWaitE4, "",
               "w 48\n");
}

TEST(InferredClockFormalRun, DISABLED_ABooleanReadTakesTheDefaultClocking) {
  ExpectEndsIn(kInferredFormalE4, BooleanAfterWait(), "", "r 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AProgramProcedureTakesItsInferredClock) {
  ExpectEndsIn(kInferredFormalE4, ProgramProcedure(), "", "p 25\n");
}

TEST(InferredClockFormalRun, DISABLED_ACheckerProcedureTakesItsInferredClock) {
  ExpectEndsIn(kInferredFormalE4, CheckerProcedure(), "", "k 25\n");
}

TEST(InferredClockFormalRun,
     DISABLED_AProcedureWithSeveralEventControlsTakesTheDefault) {
  ExpectEndsIn(kInferredFormalE4, WaitAmongSeveral(), "", "w 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AnAssertionTakesItsFlowingClock) {
  ExpectEndsIn(kInferredFormalE4, AssertionOnA(), "", "c 25\n");
}

TEST(InferredClockFormalRun, DISABLED_ASequenceBodyTakesItsClock) {
  ExpectEndsIn(kInferredFormalE4, SequenceBodyOnA(), "", "s2 25\n");
}

TEST(InferredClockFormalRun,
     DISABLED_AnActualTakesTheClockOfItsFormalsSequence) {
  ExpectEndsIn(kInferredFormalE4, kActualOfAnotherClock, "", "e6 43\ne6 43\n");
}

TEST(InferredClockFormalRun, DISABLED_MatchedReadsAClockedSequenceThatNestsIt) {
  ExpectEndsIn(kInferredFormalE4, kMatchedFromClockedSequence, "", "m 45\n");
}

TEST(InferredClockFormalRun, DISABLED_AnEventControlTakesTheDefaultClocking) {
  ExpectEndsIn(kInferredFormalE4, EventControlInInitial(), "", "ev 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AnActionBlockTakesTheLeadingClock) {
  ExpectEndsIn(kInferredFormalE4, ActionBlock(), "", "ab 25\n");
}

TEST(InferredClockFormalRun, DISABLED_AnInterfaceTakesItsOwnDefaultClocking) {
  ExpectEndsIn(kInferredFormalE4, InterfaceDefault(), InterfaceDeclaration(),
               "i 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AProgramTakesItsOwnDefaultClocking) {
  ExpectEndsIn(kInferredFormalE4, ProgramDefault(), "", "w 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AGenerateBlockTakesTheModulesDefault) {
  ExpectEndsIn(kInferredFormalE4, GenerateWait(), "", "g 48\n");
}

TEST(MethodClockInferenceRun, AGenerateBlockTakesTheModulesDefault) {
  ExpectEndsIn(kClocklessE4, GenerateWait(), "", "g 48\n");
}

const char* const kPackageSequences =
    "package pk;\n"
    "  sequence e4p(x, y); x ##1 y; endsequence\n"
    "  sequence e4f(x, y, event ck = $inferred_clock); @(ck) x ##1 y; "
    "endsequence\n"
    "endpackage\n";

const char* const kUnitSequences =
    "sequence e4p(x, y); x ##1 y; endsequence\n"
    "sequence e4f(x, y, event ck = $inferred_clock); @(ck) x ##1 y; "
    "endsequence\n";

std::string ImportedWaits(const std::string& prefix) {
  return std::string(kDefaultOnD) + "  initial forever begin wait (" + prefix +
         "e4p(b, c).triggered); $display(\"p %0t\", $time); #1; end\n"
         "  initial forever begin wait (" +
         prefix + "e4f(b, c).triggered); $display(\"f %0t\", $time); #1; end\n";
}

void ExpectEndsAfter(const std::string& before, const std::string& items,
                     const char* expected) {
  std::string src =
      before + "module t;\n" + kInferenceSignals + items + "endmodule\n";
  EXPECT_EQ(PlacedSortedVerdicts(RunPlaced(src).lines), expected) << src;
}

TEST(InferredClockFormalRun, DISABLED_APackageSequenceTakesTheModulesClock) {
  ExpectEndsAfter(kPackageSequences, ImportedWaits("pk::"), "f 48\np 48\n");
}

TEST(InferredClockFormalRun,
     DISABLED_ACompilationUnitSequenceTakesTheModulesClock) {
  ExpectEndsAfter(kUnitSequences, ImportedWaits(""), "f 48\np 48\n");
}

const char* const kGivenChecker =
    "  checker chk(logic in1, logic cd);\n"
    "    default clocking cbc @(posedge cd); endclocking\n"
    "    c1: cover property (in1) $display(\"c %0t\", $time);\n"
    "    always_ff @(posedge cd) if (in1) $display(\"k %0t\", $time);\n"
    "  endchecker\n";

const char* const kGivenUntypedChecker =
    "  checker chk(in1, cd);\n"
    "    default clocking cbc @(posedge cd); endclocking\n"
    "    c1: cover property (in1) $display(\"c %0t\", $time);\n"
    "  endchecker\n";

const char* const kSequenceFormalChecker =
    "  checker chs(sequence s, logic cd);\n"
    "    default clocking cbc @(posedge cd); endclocking\n"
    "    c1: cover property (s.triggered) $display(\"c %0t\", $time);\n"
    "    always_ff @(posedge cd) if (s.triggered) $display(\"k %0t\", "
    "$time);\n"
    "  endchecker\n";

const char* const kClockedG4 =
    "  sequence g4; @(posedge clk_d) b ##1 c; endsequence\n";

TEST(CheckerSequenceActualRun, DISABLED_AClockedTriggeredActualOfALogicFormal) {
  ExpectEndsIn(kClockedG4,
               std::string(kGivenChecker) + "  chk k1(g4.triggered, clk_d);\n",
               "", "c 48\nk 48\n");
}

TEST(CheckerSequenceActualRun,
     DISABLED_AClocklessTriggeredActualTakesTheCheckersDefault) {
  ExpectEndsIn(kClocklessE4,
               std::string(kGivenChecker) + "  chk k1(e4.triggered, clk_d);\n",
               "", "c 48\nk 48\n");
}

TEST(CheckerSequenceActualRun,
     DISABLED_AClocklessTriggeredActualOfAnUntypedFormal) {
  ExpectEndsIn(
      kClocklessE4,
      std::string(kGivenUntypedChecker) + "  chk k1(e4.triggered, clk_d);\n",
      "", "c 48\n");
}

TEST(CheckerSequenceActualRun, DISABLED_AnInstanceWithArgumentsAsTheActual) {
  ExpectEndsIn(
      "  sequence e4a(x); b ##1 x; endsequence\n",
      std::string(kGivenChecker) + "  chk k1(e4a(c).triggered, clk_d);\n", "",
      "c 48\nk 48\n");
}

TEST(CheckerSequenceActualRun,
     DISABLED_AClocklessSequenceFormalTakesTheCheckersDefault) {
  ExpectEndsIn(kClocklessE4,
               std::string(kSequenceFormalChecker) + "  chs k1(e4, clk_d);\n",
               "", "c 48\nk 48\n");
}

TEST(CheckerSequenceActualRun,
     DISABLED_AClockedSequenceFormalUnderTheCheckersDefault) {
  ExpectEndsIn(kClockedG4,
               std::string(kSequenceFormalChecker) + "  chs k1(g4, clk_d);\n",
               "", "c 48\nk 48\n");
}

TEST(CheckerSequenceActualRun,
     DISABLED_AClockedSequenceFormalUnderItsOwnClock) {
  ExpectEndsIn(kClockedG4,
               "  checker chs(sequence s, logic cd);\n"
               "    c1: cover property (@(posedge cd) s.triggered)\n"
               "      $display(\"c %0t\", $time);\n"
               "  endchecker\n"
               "  chs k1(g4, clk_d);\n",
               "", "c 48\n");
}

TEST(CheckerSequenceActualRun, DISABLED_TheCheckersDefaultOutranksTheModules) {
  ExpectEndsIn(kClocklessE4,
               "  default clocking cb @(posedge clk_a); endclocking\n" +
                   std::string(kSequenceFormalChecker) + kGivenChecker +
                   "  chs k1(e4, clk_d);\n  chk k2(e4.triggered, clk_d);\n",
               "", "c 48\nc 48\nk 48\nk 48\n");
}

TEST(CheckerSequenceActualRun, DISABLED_AnAssertionsClockWithNoCheckerDefault) {
  ExpectEndsIn(kClocklessE4,
               "  checker chk(logic in1, logic ce);\n"
               "    c1: cover property (@(posedge ce) in1) $display(\"c %0t\", "
               "$time);\n"
               "  endchecker\n"
               "  chk k1(e4.triggered, clk_e);\n",
               "", "c 43\n");
}

TEST(CheckerSequenceActualRun, MatchedOfASequenceFormalOnAnotherClock) {
  ExpectEndsIn(kClockedG4,
               "  checker chs(sequence s, logic ca);\n"
               "    c1: cover property (@(posedge ca) s.matched)\n"
               "      $display(\"m %0t\", $time);\n"
               "  endchecker\n"
               "  chs k1(g4, clk_a);\n",
               "", "m 55\n");
}

const char* const kOuterChecker =
    "  checker outer(sequence s, logic cd);\n"
    "    chs inner(s, cd);\n"
    "    chk inner2(s.triggered, cd);\n"
    "  endchecker\n";

TEST(CheckerSequenceActualRun,
     DISABLED_ACheckerPassesItsSequenceToAnInnerChecker) {
  ExpectEndsIn(kClocklessE4,
               std::string(kSequenceFormalChecker) + kGivenChecker +
                   kOuterChecker + "  outer k1(e4, clk_d);\n",
               "", "c 48\nc 48\nk 48\nk 48\n");
}

TEST(CheckerSequenceActualRun,
     DISABLED_AProceduralInstanceIsClockedInsideTheChecker) {
  ExpectEndsIn(kClocklessE4,
               std::string(kGivenChecker) +
                   "  always @(posedge clk_a) chk k1(e4.triggered, clk_d);\n",
               "", "c 48\nk 48\n");
}

TEST(CheckerSequenceActualRun, DISABLED_ACheckerInAnInterfaceOrAProgram) {
  ExpectEndsIn(kClocklessE4,
               "  ifc u_i(clk_d, b, c);\n  prg u_p(clk_d, b, c);\n",
               std::string("checker chk(logic in1, logic cd);\n"
                           "  default clocking cbc @(posedge cd); "
                           "endclocking\n"
                           "  c1: cover property (in1) $display(\"%m %0t\", "
                           "$time);\n"
                           "endchecker\n"
                           "interface ifc(input logic clk_d, b, c);\n"
                           "  sequence e4; b ##1 c; endsequence\n"
                           "  chk k1(e4.triggered, clk_d);\n"
                           "endinterface\n"
                           "program prg(input logic clk_d, b, c);\n"
                           "  sequence e4; b ##1 c; endsequence\n"
                           "  chk k1(e4.triggered, clk_d);\n"
                           "endprogram\n"),
               "t.u_i.k1 48\nt.u_p.k1 48\n");
}

const char* const kCheckerOutside =
    "  checker chk(logic in1, logic cd);\n"
    "    default clocking cbc @(posedge cd); endclocking\n"
    "    c1: cover property (in1) $display(\"c %0t\", $time);\n"
    "  endchecker\n";

TEST(CheckerSequenceActualRun, DISABLED_APackageOrCompilationUnitChecker) {
  ExpectEndsAfter(std::string("package pk;\n") + kCheckerOutside +
                      "endpackage\n" + kCheckerOutside,
                  std::string(kClocklessE4) +
                      "  pk::chk k1(e4.triggered, clk_d);\n"
                      "  chk k2(e4.triggered, clk_d);\n",
                  "c 48\nc 48\n");
}

const char* const kPortReaders =
    "interface ifc(input logic x);\n"
    "  always @(posedge x) $display(\"ifc %0t\", $time);\n"
    "endinterface\n"
    "program prg(input logic x);\n"
    "  initial forever @(posedge x) $display(\"prg %0t\", $time);\n"
    "endprogram\n"
    "module mod_adder(input logic x);\n"
    "  always @(posedge x) $display(\"%m %0t\", $time);\n"
    "endmodule\n";

TEST(PortSequenceActualRun, DISABLED_AModulePortConnectedByPosition) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) + "  mod_adder u(e4.triggered);\n",
               kPortReaders, "t.u 48\n");
}

TEST(PortSequenceActualRun, DISABLED_AModulePortConnectedByName) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) + "  mod_adder u(.x(e4.triggered));\n",
               kPortReaders, "t.u 48\n");
}

TEST(PortSequenceActualRun, DISABLED_AnExplicitlyClockedSequenceOnAModulePort) {
  ExpectEndsIn("  sequence e4; @(posedge clk_d) b ##1 c; endsequence\n",
               "  mod_adder u(e4.triggered);\n", kPortReaders, "t.u 48\n");
}

TEST(PortSequenceActualRun, DISABLED_AnInterfacePort) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) + "  ifc u(e4.triggered);\n",
               kPortReaders, "ifc 48\n");
}

TEST(PortSequenceActualRun, DISABLED_AProgramPort) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) + "  prg u(e4.triggered);\n",
               kPortReaders, "prg 48\n");
}

TEST(PortSequenceActualRun, DISABLED_TheInstantiatingModulesDefaultIsUsed) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) + "  mod_own u(e4.triggered);\n",
               "module mod_own(input logic x);\n"
               "  logic ck = 0;\n"
               "  always #5 ck = ~ck;\n"
               "  default clocking co @(posedge ck); endclocking\n"
               "  always @(posedge x) $display(\"own %0t\", $time);\n"
               "endmodule\n",
               "own 48\n");
}

TEST(PortSequenceActualRun, DISABLED_AnInstanceInAGenerateBlock) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) +
                   "  if (1) begin : g mod_adder u(e4.triggered); end\n",
               kPortReaders, "t.g.u 48\n");
}

const char* const kShowRoutines =
    "    function automatic void show(logic v);\n"
    "      if (v) $display(\"f %0t\", $time);\n"
    "    endfunction\n"
    "    task automatic tk(logic v);\n"
    "      if (v) $display(\"t %0t\", $time);\n"
    "    endtask\n";

TEST(PortSequenceActualRun, AFunctionOrTaskArgumentInAProgram) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) + "  program p;\n" + kShowRoutines +
                   "    initial forever begin\n"
                   "      wait (e4.triggered); show(e4.triggered); "
                   "tk(e4.triggered); #1;\n"
                   "    end\n"
                   "  endprogram\n"
                   "  p u_p();\n",
               "", "f 48\nt 48\n");
}

TEST(PortSequenceActualRun,
     DISABLED_AnArgumentInAProcedureTakesItsInferredClock) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) + "  program p;\n" + kShowRoutines +
                   "    initial forever @(posedge clk_a) begin\n"
                   "      show(e4.triggered); tk(e4.triggered);\n"
                   "    end\n"
                   "  endprogram\n"
                   "  p u_p();\n",
               "", "f 25\nt 25\n");
}

TEST(PortSequenceActualRun, AFunctionArgumentInAnAssertionTakesItsClock) {
  ExpectEndsIn(kClocklessE4,
               std::string(kDefaultOnD) +
                   "  function automatic logic id(logic v); return v; "
                   "endfunction\n"
                   "  c1: cover property (@(posedge clk_a) id(e4.triggered))\n"
                   "    $display(\"c %0t\", $time);\n",
               "", "c 25\n");
}

TEST(InferredClockFormalRun, DISABLED_ACheckerActualTakesTheCheckersDefault) {
  ExpectEndsIn(kInferredFormalE4,
               std::string(kSequenceFormalChecker) + kGivenChecker +
                   "  chs k1(e4, clk_d);\n  chk k2(e4.triggered, clk_d);\n",
               "", "c 48\nc 48\nk 48\nk 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AModulePortTakesTheInstantiatingDefault) {
  ExpectEndsIn(kInferredFormalE4,
               std::string(kDefaultOnD) + "  mod_adder u(e4.triggered);\n",
               kPortReaders, "t.u 48\n");
}

TEST(InferredClockFormalRun, DISABLED_AnInterfaceOrProgramPortTakesTheDefault) {
  ExpectEndsIn(kInferredFormalE4,
               std::string(kDefaultOnD) +
                   "  ifc u1(e4.triggered);\n  prg u2(e4.triggered);\n",
               kPortReaders, "ifc 48\nprg 48\n");
}

TEST(InferredClockFormalRun, DISABLED_ASubroutineArgumentTakesTheCallsClock) {
  ExpectEndsIn(kInferredFormalE4,
               std::string(kDefaultOnD) + "  program p;\n" + kShowRoutines +
                   "    initial forever @(posedge clk_a) begin\n"
                   "      show(e4.triggered); tk(e4.triggered);\n"
                   "    end\n"
                   "  endprogram\n"
                   "  p u_p();\n",
               "", "f 25\nt 25\n");
}

}  // namespace
