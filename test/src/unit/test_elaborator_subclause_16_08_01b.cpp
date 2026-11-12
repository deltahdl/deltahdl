#include <gtest/gtest.h>

#include <string>

#include "helpers_sequence_formal_bench.h"

using namespace delta;

namespace {

const char kBound[] =
    "bounds a cycle delay or a repetition but is of a type other than "
    "shortint, int or longint";

const char kBoundTypedefs[] =
    "typedef byte bt_t;\n"
    "typedef shortint si_t;\n"
    "typedef int i_t;\n"
    "typedef longint li_t;\n"
    "typedef i_t ii_t;\n";

std::string BoundBench(const std::string& type) {
  return FormalBench("sequence sb(" + type + " n); @@; endsequence",
                     kBoundTypedefs);
}

const char* const kBoundBodies[] = {
    "a ##n b",         "a[*n]",       "a[=n]",       "a[->n]",  "(a ##1 b)[*n]",
    "(a ##1 b)[*1:n]", "a ##[n:4] b", "a ##[1:n] b", "a[*n:4]", "a[*1:n]",
    "a[=n:4]",         "a[=1:n]",     "a[->n:4]",    "a[->1:n]"};

TEST(SequenceFormalBound, AShortintIntOrLongintBoundsEveryForm) {
  for (const char* type : {"shortint", "int", "longint", "int signed"}) {
    for (const char* body : kBoundBodies) {
      ExpectFormAccepted(BoundBench(type), body);
    }
  }
}

TEST(SequenceFormalBound,
     DISABLED_ATypedefOrSignedBitFormOfTheThreeIsAccepted) {
  for (const char* type : {"si_t", "i_t", "li_t", "ii_t", "bit signed [15:0]",
                           "bit signed [31:0]", "bit signed [63:0]"}) {
    for (const char* body : {"a ##n b", "a[*n]", "a[->1:n]"}) {
      ExpectFormAccepted(BoundBench(type), body);
    }
  }
}

const char* const kOtherTypes[] = {"byte",
                                   "bit [3:0]",
                                   "integer",
                                   "time",
                                   "bit [31:0]",
                                   "logic signed [15:0]",
                                   "logic signed [31:0]",
                                   "bit signed [0:31]",
                                   "byte signed",
                                   "bt_t"};

TEST(SequenceFormalBound, AnotherTypeBoundingEveryFormIsReported) {
  for (const char* type : kOtherTypes) {
    for (const char* body : kBoundBodies) {
      ExpectFormReported(BoundBench(type), body, kBound);
    }
  }
}

TEST(SequenceFormalBound, DISABLED_AnUnsignedFormOfTheThreeIsReported) {
  for (const char* type :
       {"int unsigned", "shortint unsigned", "longint unsigned"}) {
    for (const char* body : {"a ##n b", "a[*n]", "a[->1:n]"}) {
      ExpectFormReported(BoundBench(type), body, kBound);
    }
  }
}

TEST(SequenceFormalBound, AFormalInsideABoundExpressionIsChecked) {
  for (const char* body : {"a ##(n+1) b", "a[*n-1:4]"}) {
    ExpectFormAccepted(BoundBench("int"), body);
    ExpectFormReported(BoundBench("byte"), body, kBound);
  }
}

TEST(SequenceFormalBound, AFormalCarryingTheTypeBeforeItIsChecked) {
  ExpectFormAccepted(FormalBench("sequence sb(int m, n); @@; endsequence"),
                     "a[*n]");
  ExpectFormReported(FormalBench("sequence sb(byte m, n); @@; endsequence"),
                     "a[*n]", kBound);
}

TEST(SequenceFormalBound, APropertyFormalBoundingADelayIsChecked) {
  const char kProperty[] =
      "property pb(TYPE n); @(posedge clk) a |-> @@; endproperty";
  for (const char* body : {"##n b", "b[*n]"}) {
    std::string accepted = FormalBench(kProperty);
    accepted.replace(accepted.find("TYPE"), 4, "int");
    ExpectFormAccepted(accepted, body);
    std::string reported = FormalBench(kProperty);
    reported.replace(reported.find("TYPE"), 4, "byte");
    ExpectFormReported(reported, body, kBound);
  }
}

TEST(SequenceFormalBound, TheClausesDelayArgumentExampleIsAccepted) {
  ExpectFormAccepted(
      FormalBench("sequence delay_arg_example(max, shortint delay1, delay2, "
                  "min);\n"
                  "    a ##delay1 b[*min:max] ##delay2 c;\n"
                  "  endsequence\n"
                  "  parameter my_delay = 2;\n"
                  "  cover property (@(posedge clk) @@);"),
      "delay_arg_example($, my_delay, my_delay-1, 3)");
}

TEST(SequenceFormalBound, EveryPlaceAcceptsAnIntBound) {
  for (const auto& placed :
       InEveryDeclarationPlace("sequence sb(int n); @@; endsequence", "")) {
    ExpectFormAccepted(placed.source, "a[*n]");
  }
}

TEST(SequenceFormalBound, AModuleOrUnitReportsAByteBound) {
  for (const auto& placed :
       InEveryDeclarationPlace("sequence sb(byte n); @@; endsequence", "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectFormReported(placed.source, "a[*n]", kBound);
    }
  }
}

TEST(SequenceFormalBound, DISABLED_EveryOtherPlaceReportsAByteBound) {
  for (const auto& placed :
       InEveryDeclarationPlace("sequence sb(byte n); @@; endsequence", "")) {
    if (!InAModuleOrUnit(placed)) {
      ExpectFormReported(placed.source, "a[*n]", kBound);
    }
  }
}

const char kAssigned[] = "is assigned in a sequence match item";

std::string MatchBench(const std::string& formals) {
  return FormalBench("sequence sm(" + formals +
                     "); (a, @@) ##1 b; endsequence");
}

const char* const kWrites[] = {"x = 1",    "x++",      "x += 1",      "x -= 1",
                               "x *= 2",   "x /= 2",   "x %= 2",      "x &= 1",
                               "x |= 1",   "x ^= 1",   "x <<= 1",     "x >>= 1",
                               "x <<<= 1", "x >>>= 1", "x--",         "++x",
                               "--x",      "x[0] = 1", "x[1:0] += 1", "x[0]++"};

TEST(SequenceFormalMatchItem, EveryWriteOfALocalInoutFormalIsAccepted) {
  for (const char* write : kWrites) {
    ExpectFormAccepted(MatchBench("local inout int x"), write);
  }
}

TEST(SequenceFormalMatchItem, EveryWriteOfATypedFormalIsReported) {
  for (const char* write : kWrites) {
    ExpectFormReported(MatchBench("int x"), write, kAssigned);
  }
}

std::string PropertyMatchBench(const std::string& formals) {
  return FormalBench("property pm(" + formals +
                     "); @(posedge clk) (a, @@) |-> b; endproperty");
}

TEST(SequenceFormalMatchItem, EveryWriteOfALocalPropertyFormalIsAccepted) {
  for (const char* write : kWrites) {
    ExpectFormAccepted(PropertyMatchBench("local input int x"), write);
  }
}

TEST(SequenceFormalMatchItem, EveryWriteOfATypedPropertyFormalIsReported) {
  for (const char* write : kWrites) {
    ExpectFormReported(PropertyMatchBench("int x"), write, kAssigned);
  }
}

TEST(SequenceFormalMatchItem, ARealSequenceOrEventFormalIsReported) {
  ExpectFormReported(MatchBench("real x"), "x += 1.0", kAssigned);
  ExpectFormReported(MatchBench("sequence x"), "x = 1", kAssigned);
  ExpectFormReported(MatchBench("event x"), "x = 1", kAssigned);
}

TEST(SequenceFormalMatchItem, ACarriedOrLaterTypedFormalIsReported) {
  ExpectFormReported(MatchBench("int x, y"), "y = 1", "'y' of");
  const std::string kAfterLocal = MatchBench("local inout int x, int y");
  ExpectFormReported(kAfterLocal, "y += 1, x += 1", "'y' of");
  ExpectFormReported(kAfterLocal, "y += 1, x += 1", "'x' of", "@@", 0);
}

TEST(SequenceFormalMatchItem, TwoItemsWritingOneFormalReportTwice) {
  ExpectFormReported(MatchBench("int x"), "x = 1, x++", "'x' of", "@@", 2);
}

TEST(SequenceFormalMatchItem, EveryPlaceAcceptsALocalInoutWrite) {
  for (const auto& placed : InEveryDeclarationPlace(
           "sequence sm(local inout int x); (a, @@) ##1 b; endsequence", "")) {
    ExpectFormAccepted(placed.source, "x += 1");
  }
}

const char kTypedWrites[] =
    "sequence sm(int x); (a, @@) ##1 b; endsequence\n"
    "  property pm(int x); @(posedge clk) (a, @@) |-> b; endproperty";

void ExpectBothWritesReported(const PlacedSource& placed) {
  ExpectFormReported(placed.source, "x += 1", "'x' of 'sm'");
  ExpectFormReported(placed.source, "x += 1", "'x' of 'pm'", "(a, @@) |->");
}

TEST(SequenceFormalMatchItem, AModuleOrUnitReportsATypedWrite) {
  for (const auto& placed : InEveryDeclarationPlace(kTypedWrites, "")) {
    if (InAModuleOrUnit(placed)) ExpectBothWritesReported(placed);
  }
}

TEST(SequenceFormalMatchItem, DISABLED_EveryOtherPlaceReportsATypedWrite) {
  for (const auto& placed : InEveryDeclarationPlace(kTypedWrites, "")) {
    if (!InAModuleOrUnit(placed)) ExpectBothWritesReported(placed);
  }
}

TEST(SequenceFormalMatchItem, EveryLocalOrUntypedFormalWriteIsAccepted) {
  ExpectFormAccepted(MatchBench("local input int x"), "x = 1");
  ExpectFormAccepted(MatchBench("local input int x"), "x++");
  ExpectFormAccepted(MatchBench("local output int x"), "x = 1");
  ExpectFormAccepted(MatchBench("local int x"), "x--");
  ExpectFormAccepted(MatchBench("local inout int x, y"), "y += 1");
  ExpectFormAccepted(MatchBench("int x, untyped y"), "y = 1");
  ExpectFormAccepted(PropertyMatchBench("local input int x"), "x = 1");
  ExpectFormAccepted(
      FormalBench("sequence sv(int x); int v; (a, @@) ##1 b; endsequence"),
      "v = x + 1");
}

}  // namespace
