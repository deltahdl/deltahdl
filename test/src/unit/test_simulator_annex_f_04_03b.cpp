#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Clocks() {
  return "  bit clk = 0, clk1 = 0, clk2 = 0, clk3 = 0, f = 1;\n"
         "  bit z = 0, o = 1, rst = 0;\n  int now = 4;\n"
         "  initial begin #12 now = 14; #4 now = 17; #4 now = 21; #10 now = "
         "37; "
         "#10 now = 0; end\n  always #5 clk = ~clk;\n"
         "  initial begin #18 clk1 = 1; forever #10 clk1 = ~clk1; end\n"
         "  initial begin #22 clk2 = 1; forever #10 clk2 = ~clk2; end\n"
         "  initial begin #2 clk3 = 1; #1 clk3 = 0; #2 clk3 = 1; forever #10 "
         "clk3 = ~clk3; end\n"
         "  initial #7 f = 0;\n"
         "  initial begin #100 $display(\"done\"); $finish; end\n";
}

std::size_t Lines(const std::string& text, const std::string& line) {
  std::size_t count = 0;
  for (std::size_t at = text.find(line); at != std::string::npos;
       at = text.find(line, at + line.size())) {
    ++count;
  }
  return count;
}

std::string Replaced(std::string text, const std::string& from,
                     const std::string& to) {
  for (std::size_t at = text.find(from); at != std::string::npos;
       at = text.find(from, at + to.size())) {
    text.replace(at, from.size(), to);
  }
  return text;
}

void ExpectHits(const std::string& src, std::size_t hits) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_EQ(Lines(out, "done\n"), 1u) << src << out;
  EXPECT_EQ(Lines(out, "hit\n"), hits) << src << out;
}

std::string Module(const std::string& before, const std::string& items) {
  return before + "module t;\n" + Clocks() + items + "endmodule\n";
}

std::string Check(const std::string& text, const std::string& op, int value) {
  return Replaced(text, "CHECK",
                  "(v " + op + " " + std::to_string(value) + ")");
}

void ExpectFailsUnlessHeld(const std::string& src, int value) {
  ExpectHits(Check(src, "==", value), 0);
  ExpectHits(Check(src, "!=", value), 1);
}

void ExpectFailsWhenHeld(const std::string& src, int value) {
  ExpectHits(Check(src, "==", value), 1);
  ExpectHits(Check(src, "!=", value), 0);
}

std::string Directive(const std::string& verb, const std::string& spec) {
  return "  " + verb + " property (@(posedge clk) " + spec +
         ") else $display(\"hit\");\n";
}

std::string Sequence(const std::string& body) {
  return "  sequence r; int v = now; " + body + "; endsequence\n";
}

std::string Property(const std::string& body) {
  return "  property p; int v = now; " + body + "; endproperty\n";
}

void ExpectSequence(const std::string& body, const std::string& spec,
                    int value) {
  ExpectFailsUnlessHeld(Module("", Sequence(body) + Directive("assert", spec)),
                        value);
}

void ExpectProperty(const std::string& body, int value) {
  ExpectFailsUnlessHeld(
      Module("", Property(body) + Directive("assert", "f |=> p")), value);
}

void ExpectInvertedProperty(const std::string& body, int value) {
  ExpectFailsWhenHeld(
      Module("", Property(body) + Directive("assert", "f |=> p")), value);
}

std::string EmptyRest(const std::string& rest, const std::string& spec) {
  return Module("", "  sequence r; int v = now; " + rest +
                        "; endsequence\n"
                        "  cover property (@(posedge clk) " +
                        spec + ") $display(\"hit\");\n");
}

TEST(SequenceInitializer, AnEmptyMatchOfTheRestIsKept) {
  ExpectHits(EmptyRest("z[*0:1]", "f ##1 r"), 1);
  ExpectHits(EmptyRest("z", "f ##1 r"), 0);
}

TEST(SequenceInitializer, AnEmptyMatchOfTheRestDoesNotFuse) {
  ExpectHits(EmptyRest("z[*0:1]", "f ##0 r"), 0);
  ExpectHits(EmptyRest("(o && v == 4)[*0:1]", "f ##0 r"), 1);
}

TEST(SequenceInitializer, ItRunsAtTheRestsOwnClock) {
  ExpectSequence("@(posedge clk1) CHECK", "f |=> r", 17);
  ExpectSequence("@(posedge clk1) CHECK[*1:$] ##0 o", "f |=> r", 17);
}

TEST(SequenceInitializer, AMulticlockedRestReadsOneCopyAtItsLeadingClock) {
  ExpectSequence("@(posedge clk1) CHECK ##1 @(posedge clk2) 1", "f |=> r", 17);
  ExpectSequence("@(posedge clk1) 1 ##1 @(posedge clk2) CHECK", "f |=> r", 17);
}

TEST(SequenceInitializer, ItRunsAtAClockTickingAsTheAttemptBegins) {
  ExpectSequence("@(posedge clk3) CHECK", "f |-> r", 4);
  ExpectSequence("@(posedge clk3) CHECK", "f ##0 o |-> r", 4);
}

TEST(SequenceInitializer, ItRunsAtAClockTickingAsAFusedInstanceBegins) {
  ExpectSequence("@(posedge clk3) CHECK", "f |-> o ##0 r", 4);
}

std::string FormalReader() {
  return "  sequence r(c, x); int v = x; @(posedge c) CHECK; endsequence\n";
}

TEST(SequenceInitializer, AFormalIsReadAtTheLeadingClock) {
  ExpectFailsUnlessHeld(
      Module("", FormalReader() + Directive("assert", "f |=> r(clk1, now)")),
      17);
}

TEST(SequenceInitializer, ALaterLocalReadsAnEarlierOneAtTheLeadingClock) {
  ExpectFailsUnlessHeld(
      Module("",
             "  sequence r; int w = now; int v = w; @(posedge clk1) CHECK; "
             "endsequence\n" +
                 Directive("assert", "f |=> r")),
      17);
}

TEST(SequenceInitializer, AnAssumptionsInstanceInitializesAtTheClock) {
  ExpectFailsUnlessHeld(Module("", Sequence("@(posedge clk1) CHECK") +
                                       Directive("assume", "f |=> r")),
                        17);
}

TEST(SequenceInitializer, ACoversInstanceInitializesAtTheClock) {
  std::string src = Module("", Sequence("@(posedge clk1) CHECK") +
                                   "  cover property (r) $display(\"hit\");\n");
  ExpectHits(Check(src, "==", 17), 1);
  ExpectHits(Check(src, "==", 37), 1);
  ExpectHits(Check(src, "==", 16), 0);
}

std::string Element(const std::string& keyword, const std::string& ports) {
  return keyword + " sub" + ports + ";\n" + FormalReader() +
         Directive("assert", "f |=> r(clk1, now)") + "end" + keyword + "\n";
}

std::string VariablePorts() {
  return "(input var bit clk, input var bit clk1, input var bit f, input var "
         "int now)";
}

void ExpectElement(const std::string& element) {
  ExpectFailsUnlessHeld(Module(element, "  sub u(clk, clk1, f, now);\n"), 17);
}

TEST(SequenceInitializer, AnInterfacesSequenceInitializesAtTheClock) {
  ExpectElement(Element("interface", VariablePorts()));
}

TEST(SequenceInitializer, AProgramsSequenceInitializesAtTheClock) {
  ExpectElement(Element("program", VariablePorts()));
}

TEST(SequenceInitializer, ACheckersSequenceInitializesAtTheClock) {
  ExpectElement(Element("checker", "(clk, clk1, f, int now)"));
}

TEST(SequenceInitializer, APackagesSequenceInitializesAtTheClock) {
  ExpectFailsUnlessHeld(
      Module("package pk;\n" + FormalReader() + "endpackage\n",
             Directive("assert", "f |=> pk::r(clk1, now)")),
      17);
}

TEST(PropertyInitializer, DISABLED_ANonoverlappingAntecedentThatCanBeEmpty) {
  ExpectProperty("@(posedge clk1) z[*0:1] |=> CHECK", 17);
}

TEST(PropertyInitializer, ANonoverlappingAntecedentThatCannotBeEmpty) {
  ExpectProperty("@(posedge clk1) o |=> CHECK", 17);
}

TEST(PropertyInitializer, AnOverlappingAntecedentThatCanBeEmpty) {
  ExpectProperty("@(posedge clk1) o[*0:1] |-> CHECK", 17);
}

std::string Disabled(const std::string& pulse) {
  return Module("", Property("disable iff (rst) @(posedge clk) f |=> "
                             "@(posedge clk1) CHECK") +
                        pulse +
                        "  assert property (p) else $display(\"hit\");\n");
}

TEST(PropertyInitializer, ADisabledAttemptReadsNoCopy) {
  std::string src = Disabled("  initial begin #8 rst = 1; #20 rst = 0; end\n");
  ExpectHits(Check(src, "==", 4), 0);
  ExpectHits(Check(src, "!=", 4), 0);
}

TEST(PropertyInitializer,
     DISABLED_AnUndisabledAttemptReadsItsLeadingClocksCopy) {
  ExpectFailsUnlessHeld(Disabled(""), 4);
}

TEST(PropertyInitializer, AnUndisabledAttemptInitializesAtItsClock) {
  std::string src = Module("", Property("disable iff (rst) @(posedge clk1) "
                                        "o |-> CHECK") +
                                   "  assert property (p) else "
                                   "$display(\"hit\");\n");
  ExpectHits(Check(src, "!=", 17), 1);
  ExpectHits(Check(src, "!=", 37), 1);
  ExpectHits(Check(src, "!=", 16), 0);
}

TEST(PropertyInitializer, ParenthesesInitializeAtTheClockInside) {
  ExpectProperty("(@(posedge clk1) o |-> CHECK)", 17);
}

TEST(PropertyInitializer, DISABLED_ANegationInitializesAtItsOperandsClock) {
  ExpectInvertedProperty("not (@(posedge clk1) CHECK)", 17);
}

TEST(PropertyInitializer, DISABLED_AnAbortInitializesAtItsOperandsClock) {
  ExpectProperty("accept_on (rst) (@(posedge clk1) o |-> CHECK)", 17);
  ExpectProperty("reject_on (rst) (@(posedge clk1) o |-> CHECK)", 17);
}

TEST(PropertyInitializer, EachClockOfAnOrHasItsOwnCopy) {
  ExpectProperty("(@(posedge clk1) CHECK) or (@(posedge clk2) z)", 17);
  ExpectProperty("(@(posedge clk1) z) or (@(posedge clk2) CHECK)", 21);
}

TEST(PropertyInitializer, AnOrOnOneClockHasOneCopy) {
  ExpectProperty("(@(posedge clk1) z) or (@(posedge clk1) CHECK)", 17);
  ExpectProperty("(@(posedge clk1) CHECK) or (@(posedge clk1) z)", 17);
}

TEST(PropertyInitializer, AnAndOnOneClockHasOneCopy) {
  ExpectProperty("(@(posedge clk1) o) and (@(posedge clk1) CHECK)", 17);
  ExpectProperty("(@(posedge clk1) CHECK) and (@(posedge clk1) o)", 17);
}

TEST(PropertyInitializer, AConditionalInitializesBeforeItsBranch) {
  ExpectProperty("@(posedge clk1) if (o) CHECK else o", 17);
  ExpectProperty("@(posedge clk1) if (z) o else CHECK", 17);
}

TEST(PropertyInitializer, AMulticlockedImplicationsAntecedentReadsTheFirst) {
  ExpectInvertedProperty("@(posedge clk1) CHECK |=> @(posedge clk2) z", 17);
}

TEST(PropertyInitializer, DISABLED_AFormalIsReadAtTheLeadingClock) {
  ExpectFailsUnlessHeld(
      Module(
          "",
          "  property p(x); int v = x; @(posedge clk1) CHECK; endproperty\n" +
              Directive("assert", "f |=> p(now)")),
      17);
}

}  // namespace
