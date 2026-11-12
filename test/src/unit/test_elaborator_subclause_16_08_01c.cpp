#include <gtest/gtest.h>

#include <string>

#include "helpers_sequence_formal_bench.h"

using namespace delta;

namespace {

const char kSequenceActual[] = "takes a sequence expression";
const char kSequenceRef[] = "of type sequence";

const char kSequenceTaker[] =
    "sequence s1(sequence q); c ##1 q; endsequence\n"
    "  sequence ab; @(posedge clk) a ##1 b; endsequence\n"
    "  cover property (@(posedge clk) @@);";

TEST(SequenceFormalActual, DISABLED_AnEdgeOrPropertyActualIsReported) {
  for (const char* actual :
       {"s1(posedge clk)", "s1(negedge clk)", "s1(not a)", "s1(a |-> b)"}) {
    ExpectFormReported(FormalBench(kSequenceTaker), actual, kSequenceActual);
  }
}

TEST(SequenceFormalActual, ASequenceBooleanOrClockedActualIsAccepted) {
  for (const char* actual : {"s1(a ##1 b)", "s1(clk)", "s1(a)", "s1(ab)",
                             "s1(@(posedge clk) a ##1 b)"}) {
    ExpectFormAccepted(FormalBench(kSequenceTaker), actual);
  }
}

std::string SequenceDefault(const std::string& actual) {
  return FormalBench("sequence s1(sequence q = " + actual +
                     "); c ##1 q; endsequence\n"
                     "  cover property (@(posedge clk) @@);");
}

TEST(SequenceFormalActual, DISABLED_ADefaultThatIsNoSequenceIsReported) {
  for (const char* actual : {"posedge clk", "not a"}) {
    ExpectFormReported(SequenceDefault(actual), "s1()", kSequenceActual,
                       "sequence q =");
  }
}

TEST(SequenceFormalActual, ASequenceDefaultIsAccepted) {
  ExpectFormAccepted(SequenceDefault("a ##1 b"), "s1()");
}

std::string SequenceUse(const std::string& body) {
  return FormalBench(
      "sequence sb(bit x); x; endsequence\n"
      "  sequence sq(sequence x); x; endsequence\n"
      "  sequence su(x); x; endsequence\n"
      "  sequence sr(sequence q); int v; " +
      body +
      "; endsequence\n"
      "  cover property (@(posedge clk) sr(a ##1 b));");
}

const char* const kBooleanUses[] = {"q == 1",   "!q",    "q && b",
                                    "$rose(q)", "sb(q)", "q[=2]"};

TEST(SequenceFormalReference, DISABLED_ABooleanUseOfTheFormalIsReported) {
  for (const char* use : kBooleanUses) {
    ExpectFormReported(SequenceUse("@@"), use, kSequenceRef);
  }
  ExpectFormReported(SequenceUse("(c, @@) ##1 b"), "v = q", kSequenceRef);
}

TEST(SequenceFormalReference, ATriggeredOrSequenceUseIsAccepted) {
  for (const char* use : {"q.triggered == 1", "q.triggered && b",
                          "$rose(q.triggered)", "sq(q)", "su(q)", "q[*2]"}) {
    ExpectFormAccepted(SequenceUse("@@"), use);
  }
  ExpectFormAccepted(SequenceUse("(c, @@) ##1 b"), "v = q.triggered");
}

const char* const kSequenceOperands[] = {
    "q[*2]",      "q[+]",           "q[*] ##1 a",     "q ##1 a",
    "a ##1 q",    "q and a",        "a and q",        "q or a",
    "a or q",     "q intersect a",  "a intersect q",  "q within a",
    "a within q", "a throughout q", "first_match(q)", "q.matched"};

TEST(SequenceFormalReference, EverySequenceOperandPlaceIsAccepted) {
  for (const char* use : kSequenceOperands) {
    ExpectFormAccepted(SequenceUse("@@"), use);
  }
}

TEST(SequenceFormalReference, EveryPlaceAcceptsTheFormalAsASequence) {
  for (const auto& placed : InEveryDeclarationPlace(
           "sequence sr(sequence q); c ##1 @@; endsequence", "")) {
    ExpectFormAccepted(placed.source, "q");
  }
}

TEST(SequenceFormalReference, DISABLED_EveryPlaceReportsABooleanUse) {
  for (const auto& placed : InEveryDeclarationPlace(
           "sequence sr(sequence q); c ##1 @@; endsequence", "")) {
    ExpectFormReported(placed.source, "q == 1", kSequenceRef);
  }
}

TEST(SequenceFormalActual, DISABLED_EveryPlaceReportsAnEdgeActual) {
  for (const auto& placed :
       InEveryDeclarationPlace("sequence s1(sequence q); c ##1 q; endsequence",
                               "cover property (@(posedge clk) @@);")) {
    ExpectFormReported(placed.source, "s1(posedge clk)", kSequenceActual);
  }
}

const char kEventActual[] = "takes an event expression";
const char kEventRef[] = "of type event is referenced where";

const char kEventTaker[] =
    "event ev;\n"
    "  sequence s1(event e); @(e) a ##1 b; endsequence\n"
    "  sequence t; @(posedge clk) a; endsequence\n"
    "  cover property (@@);";

TEST(EventFormalActual, DISABLED_ASequenceOrPropertyActualIsReported) {
  for (const char* actual : {"s1(a ##1 b)", "s1(.e(a ##1 b))", "s1(a |-> b)"}) {
    ExpectFormReported(FormalBench(kEventTaker), actual, kEventActual);
  }
}

TEST(EventFormalActual, DISABLED_AnActualInsideAnotherDeclarationIsReported) {
  for (const char* outer :
       {"sequence so; @@; endsequence", "property po; @@; endproperty"}) {
    ExpectFormReported(
        FormalBench(std::string("sequence s1(event e); @(e) a ##1 b; "
                                "endsequence\n  ") +
                    outer),
        "s1(a ##1 b)", kEventActual);
  }
}

TEST(EventFormalActual, EveryEventExpressionActualIsAccepted) {
  for (const char* actual : {"s1(posedge clk)", "s1(posedge clk iff c)",
                             "s1(edge clk)", "s1(posedge clk or negedge a)",
                             "s1((a, b))", "s1(clk)", "s1(ev)", "s1(t)"}) {
    ExpectFormAccepted(FormalBench(kEventTaker), actual);
  }
}

std::string EventDefault(const std::string& actual) {
  return FormalBench("sequence s1(event e = " + actual +
                     "); @(e) a ##1 b; endsequence\n"
                     "  cover property (@@);");
}

TEST(EventFormalActual, DISABLED_ASequenceDefaultIsReported) {
  ExpectFormReported(EventDefault("a ##1 b"), "s1()", kEventActual,
                     "event e =");
}

TEST(EventFormalActual, ABareSignalDefaultIsAccepted) {
  ExpectFormAccepted(EventDefault("a"), "s1()");
}

std::string EventUse(const std::string& place = "module") {
  const std::string kDecl = "sequence s1(event e); @@; endsequence";
  for (const auto& placed : InEveryDeclarationPlace(kDecl, "")) {
    if (placed.place == place) return placed.source;
  }
  return "";
}

TEST(EventFormalReference, AnOperandOrTriggeredUseIsReported) {
  for (const char* use :
       {"@(posedge clk) $rose(e)", "@(posedge clk) e.triggered"}) {
    ExpectFormReported(EventUse(), use, kEventRef);
  }
}

TEST(EventFormalReference, DISABLED_AnEdgedOrGuardingFormalIsReported) {
  for (const char* use : {"@(posedge e) a", "@(negedge e) a", "@(edge e) a",
                          "@(posedge clk iff e) a", "@(e iff c) a"}) {
    ExpectFormReported(EventUse(), use, kEventRef);
  }
}

TEST(EventFormalReference, AnEventListHoldingTheFormalIsAccepted) {
  for (const char* use :
       {"@(e or posedge clk) a", "@(e, negedge clk) a", "@(e) a", "@e a"}) {
    ExpectFormAccepted(EventUse(), use);
  }
}

TEST(EventFormalReference, DISABLED_EveryPlaceReportsAnEdgedFormal) {
  for (const char* place :
       {"interface", "program", "checker", "package", "compilation unit"}) {
    ExpectFormReported(EventUse(place), "@(posedge e) a", kEventRef);
  }
}

TEST(EventFormalReference, EveryPlaceAcceptsTheFormalAsAClock) {
  for (const char* place :
       {"interface", "program", "checker", "package", "compilation unit"}) {
    ExpectFormAccepted(EventUse(place), "@(e) a");
  }
}

}  // namespace
