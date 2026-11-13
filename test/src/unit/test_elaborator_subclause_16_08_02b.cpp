#include <gtest/gtest.h>

#include <string>

#include "helpers_sequence_formal_bench.h"

using namespace delta;

namespace {

constexpr FormalReport kTypeReport = {
    .message = "the type of a local variable formal argument must be one of",
    .subclause = "16.8.2"};

constexpr FormalReport kChandleReport = {
    .message =
        "a sequence or property formal argument may not be of type "
        "chandle",
    .subclause = "16.8"};

const char kTypeBench[] = "sequence st(@@); a; endsequence";

TEST(LocalFormalType, AChandleInEveryFormIsReported) {
  for (const char* item :
       {"local chandle h", "local input chandle h", "local inout chandle h",
        "local output chandle h", "local int a, b, local chandle h, g"}) {
    ExpectReportedAs(FormalBench(kTypeBench), item, kChandleReport);
  }
}

TEST(LocalFormalType, EveryPlaceReportsALocalChandle) {
  for (const auto& placed : InEveryDeclarationPlace(kTypeBench, "")) {
    ExpectReportedAs(placed.source, "local chandle h", kChandleReport);
  }
}

TEST(LocalFormalType, EveryPlaceAcceptsALocalInt) {
  for (const auto& placed : InEveryDeclarationPlace(kTypeBench, "")) {
    ExpectFormAccepted(placed.source, "local int h");
  }
}

TEST(LocalFormalType, DISABLED_ATypedefOfChandleOrEventIsReported) {
  ExpectReportedAs(FormalBench(kTypeBench, "typedef chandle ch_t;\n"),
                   "local ch_t h", kTypeReport);
  ExpectReportedAs(
      FormalBench(std::string("typedef chandle ch_t;\n  ") + kTypeBench),
      "local ch_t h", kTypeReport);
  ExpectReportedAs(
      FormalBench(kTypeBench, "package pk; typedef chandle ch_t; endpackage\n"),
      "local pk::ch_t h", kTypeReport);
  ExpectReportedAs(FormalBench(kTypeBench, "typedef event ev_t;\n"),
                   "local ev_t e", kTypeReport);
}

TEST(LocalFormalType, AnotherSixteenSixTypeIsAccepted) {
  const std::string kTypes =
      "package pk; typedef bit [7:0] t; endpackage\n"
      "typedef struct packed { bit [3:0] x; } ps_t;\n";
  for (const char* item : {"local real r", "local inout realtime t",
                           "local ps_t p", "local pk::t x"}) {
    ExpectFormAccepted(FormalBench(kTypeBench, kTypes), item);
  }
}

constexpr FormalReport kUnassignedActual = {
    .message = "is referenced at a point where it is unassigned",
    .subclause = "16.8.2"};

const char kTakers[] =
    "sequence sub(local input int x); a ##1 (x == 1); endsequence\n"
    "  sequence subio(local inout int x); (a, x += 1); endsequence\n"
    "  sequence sub_out(local output int o); (a, o = 1); endsequence\n"
    "  property pin(local input int x); a |-> x == 1; endproperty\n";

std::string TakerBench(const std::string& use) {
  return FormalBench(std::string(kTakers) + "  " + use);
}

const char kInSequence[] = "sequence top; int v, w; @@; endsequence";

TEST(LocalFormalActualAssigned, AnUnassignedLocalReadByAnActualIsReported) {
  for (const char* use :
       {"subio(v)", "sub(w + 1)", "((a, v = 0) or b) ##1 sub(v)",
        "(a, v = 0) ##1 sub(v) or sub(v)", "(a, v = 0) intersect sub(v)"}) {
    ExpectReportedAs(TakerBench(kInSequence), use, kUnassignedActual);
  }
}

TEST(LocalFormalActualAssigned, AnAssignedLocalReadByAnActualIsAccepted) {
  for (const char* use :
       {"(1, v = 0) ##1 sub(v)", "(1, v = 0) ##1 sub(v + 1)",
        "((a, v = 0) or (b, v = 1)) ##1 sub(v)", "sub_out(v) ##1 (v == 1)"}) {
    ExpectFormAccepted(TakerBench(kInSequence), use);
  }
  ExpectFormAccepted(TakerBench("sequence top; int v = 0; @@; endsequence"),
                     "sub(v)");
}

TEST(LocalFormalActualAssigned, AnEnclosingFormalAsTheActualIsChecked) {
  ExpectReportedAs(TakerBench("@@"),
                   "sequence s(local output int o); a ##1 sub(o) ##0 "
                   "(1, o = 1); endsequence",
                   kUnassignedActual);
  ExpectFormAccepted(TakerBench("@@"),
                     "sequence s(local input int i); a ##1 sub(i); "
                     "endsequence");
}

TEST(LocalFormalActualAssigned, ASequenceInstanceInAPropertyIsChecked) {
  ExpectReportedAs(TakerBench("@@"),
                   "property p; int v; sub(v) |-> a; endproperty",
                   kUnassignedActual);
  ExpectFormAccepted(TakerBench("@@"),
                     "property p; int v; (1, v = 0) ##1 sub(v) |-> a; "
                     "endproperty");
}

TEST(LocalFormalActualAssigned, DISABLED_APropertyInstanceIsCitedUnderLocals) {
  for (const char* use : {"property p; int v; a |-> pin(v); endproperty",
                          "property p; int v; a |-> pin(v + 1); endproperty"}) {
    ExpectReportedAs(TakerBench("@@"), use, kUnassignedActual);
  }
}

TEST(LocalFormalActualAssigned, AnAssignedPropertyActualIsAccepted) {
  for (const char* use :
       {"property p; int v; (1, v = 0) |-> pin(v); endproperty",
        "property p; int v = 3; a |-> pin(v + 1); endproperty"}) {
    ExpectFormAccepted(TakerBench("@@"), use);
  }
}

const char kActualPlace[] =
    "sequence sub(local input int x); a ##1 (x == 1); endsequence\n"
    "  sequence top; int v; @@; endsequence";

constexpr FormalReport kUnassignedActualInTop = {
    .message = kUnassignedActual.message,
    .subclause = "16.8.2",
    .at = "sequence top"};

TEST(LocalFormalActualAssigned, AModuleOrUnitReportsAnUnassignedActual) {
  for (const auto& placed : InEveryDeclarationPlace(kActualPlace, "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "sub(v)", kUnassignedActualInTop);
    }
  }
}

TEST(LocalFormalActualAssigned,
     DISABLED_EveryOtherPlaceReportsAnUnassignedActual) {
  for (const auto& placed : InEveryDeclarationPlace(kActualPlace, "")) {
    if (!InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "sub(v)", kUnassignedActualInTop);
    }
  }
}

TEST(LocalFormalActualAssigned, EveryPlaceAcceptsAnAssignedActual) {
  for (const auto& placed : InEveryDeclarationPlace(kActualPlace, "")) {
    ExpectFormAccepted(placed.source, "(1, v = 0) ##1 sub(v)");
  }
}

constexpr FormalReport kUnassignedOutput = {
    .message = "is referenced at a point where it is unassigned",
    .subclause = "16.10"};

const char kReadsFirst[] =
    "sequence s8(local output int o); (o == 1) ##0 (a, o = 2); endsequence\n";

std::string OutputBench(const std::string& direction = "output") {
  return TakerBench("sequence so(local " + direction +
                    " int o); int g; @@; endsequence");
}

TEST(LocalFormalOutputStart, AReadBeforeTheBodyAssignsIsReported) {
  for (const char* body :
       {"a ##1 (o == 1) ##0 (1, o = 2)", "(a, o++) ##1 (1, o = 2)",
        "(a, o += 1) ##1 (1, o = 2)", "(a, g = o) ##1 (1, o = 2)",
        "((a, o = 1) or b) ##1 (o == 1)"}) {
    ExpectReportedAs(OutputBench(), body, kUnassignedOutput);
  }
}

TEST(LocalFormalOutputStart, AnOutputPassedToAnInputFormalIsReported) {
  ExpectReportedAs(OutputBench(), "sub(o) ##0 (1, o = 2)", kUnassignedActual);
}

TEST(LocalFormalOutputStart, AnAssignedActualDoesNotAssignTheOutput) {
  ExpectReportedAs(
      TakerBench(std::string(kReadsFirst) +
                 "  sequence sv; int v; (a, v = 1) ##1 @@; endsequence"),
      "s8(v)",
      {.message = kUnassignedOutput.message,
       .subclause = "16.10",
       .at = "sequence s8"});
}

TEST(LocalFormalOutputStart, AReadAfterTheBodyAssignsIsAccepted) {
  for (const char* body :
       {"(a, o = 1) ##1 (o == 1)", "(a, o = 1) ##1 sub(o)"}) {
    ExpectFormAccepted(OutputBench(), body);
  }
}

TEST(LocalFormalActualAssigned, DISABLED_APackageOutputActualIsNotRead) {
  ExpectFormAccepted(
      FormalBench("sequence w; int v; @@ ##1 (v == 1); endsequence",
                  "package pk;\n  bit a;\n"
                  "  sequence so(local output int o); (a, o = 1); endsequence\n"
                  "endpackage\n"),
      "pk::so(v)");
}

TEST(LocalFormalOutputStart, AnInoutHoldsItsActualFromTheStart) {
  ExpectFormAccepted(OutputBench("inout"), "a ##1 (o == 1)");
  ExpectFormAccepted(OutputBench("inout"), "(a, g = o)");
}

std::string OutputLocalBench(const std::string& direction) {
  return FormalBench("sequence so(local " + direction +
                     " int o); int g = @@; (a, o = 1); endsequence");
}

TEST(LocalFormalOutputStart, DISABLED_ABodyLocalInitializedByAnOutputIsRep) {
  ExpectReportedAs(OutputLocalBench("output"), "o", kUnassignedOutput);
}

TEST(LocalFormalOutputStart, ABodyLocalInitializedByAnInoutIsAccepted) {
  ExpectFormAccepted(OutputLocalBench("inout"), "o");
}

const char kOutputPlace[] = "sequence so(local output int o); @@; endsequence";

TEST(LocalFormalOutputStart, AModuleOrUnitReportsAnEarlyRead) {
  for (const auto& placed : InEveryDeclarationPlace(kOutputPlace, "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "a ##1 (o == 1) ##0 (1, o = 2)",
                       kUnassignedOutput);
    }
  }
}

TEST(LocalFormalOutputStart, DISABLED_EveryOtherPlaceReportsAnEarlyRead) {
  for (const auto& placed : InEveryDeclarationPlace(kOutputPlace, "")) {
    if (!InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "a ##1 (o == 1) ##0 (1, o = 2)",
                       kUnassignedOutput);
    }
  }
}

TEST(LocalFormalOutputStart, DISABLED_AUsedPackageSequenceReportsAnEarlyRead) {
  const std::string kPackage =
      "package pk;\n  bit a;\n  sequence so(local output int o); @@; "
      "endsequence\nendpackage\n";
  for (const char* use : {"sequence w; int v; pk::so(v); endsequence",
                          "import pk::*;\n  sequence w; int v; so(v); "
                          "endsequence"}) {
    ExpectReportedAs(FormalBench(use, kPackage),
                     "a ##1 (o == 1) ##0 (1, o = 2)", kUnassignedOutput);
  }
}

TEST(LocalFormalOutputStart, DISABLED_EveryPlaceReportsABodyLocalReadingIt) {
  for (const auto& placed : InEveryDeclarationPlace(
           "sequence so(local output int o); int g = @@; (a, o = 1); "
           "endsequence",
           "")) {
    ExpectReportedAs(placed.source, "o", kUnassignedOutput);
  }
}

TEST(LocalFormalOutputStart, EveryPlaceAcceptsAReadAfterAssignment) {
  for (const auto& placed : InEveryDeclarationPlace(kOutputPlace, "")) {
    ExpectFormAccepted(placed.source, "(a, o = 1) ##1 (o == 1)");
  }
}

TEST(LocalFormalCarry, DISABLED_AnItemNamingAnotherKindOfTypeEndsTheCarry) {
  for (const char* item :
       {"local input int lv, untyped d", "local input int lv, sequence q",
        "local input int lv, event e"}) {
    ExpectFormAccepted(FormalBench(kTypeBench), item);
  }
}

TEST(LocalFormalCarry, AnItemOfAnIdentifierAloneTakesTheCarry) {
  ExpectReportedAs(FormalBench("sequence st(local output int o, @@); (a, o = "
                               "1); endsequence"),
                   "p",
                   {.message = "is unassigned at the completion of a match",
                    .subclause = "16.8.2"});
  ExpectFormAccepted(FormalBench("sequence st(local output int o, @@); (a, o = "
                                 "1); endsequence"),
                     "logic p");
}

constexpr FormalReport kUnassignedAtMatch = {
    .message = "is unassigned at the completion of a match",
    .subclause = "16.8.2"};

TEST(LocalFormalMatchCompletion, DISABLED_BothBranchesAssigningItCompleteIt) {
  ExpectFormAccepted(OutputBench(), "((a, o = 1) or (b, o = 2)) ##1 (o == 1)");
  ExpectFormAccepted(OutputBench(), "((a, o = 1) or (b, o = 2)) ##1 b");
}

TEST(LocalFormalMatchCompletion, AnInoutIsAssignedFromItsActualAtTheStart) {
  ExpectReportedAs(
      FormalBench("sequence so(local inout int o); @@; endsequence"),
      "(a, o = 1) or b",
      {.message = "is unassigned", .subclause = "16.8.2", .times = 0});
}

std::string CompletionBench() {
  return FormalBench("sequence so(local output int o); @@; endsequence");
}

TEST(LocalFormalMatchCompletion, AnOutputARepetitionMaySkipIsReported) {
  ExpectReportedAs(CompletionBench(), "a ##1 (b, o = 1) [*0:1]",
                   kUnassignedAtMatch);
}

TEST(LocalFormalMatchCompletion,
     DISABLED_AnOutputBlockedFromFlowingIsReported) {
  for (const char* body :
       {"(a, o = 1) and (b, o = 2)", "(a, o = 1) intersect (b, o = 2)",
        "(a, o = 1) within (b, o = 2) [*3]"}) {
    ExpectReportedAs(CompletionBench(), body, kUnassignedAtMatch);
  }
}

TEST(LocalFormalMatchCompletion, AnOutputEveryPathAssignsIsAccepted) {
  for (const char* body :
       {"(a, o = 1) and b", "(b, o = 1) [*1:2]", "first_match((a, o = 1))",
        "a throughout (b, o = 1)"}) {
    ExpectFormAccepted(CompletionBench(), body);
  }
}

const char kCompletionPlace[] =
    "sequence so(local output int o); @@; endsequence";

TEST(LocalFormalMatchCompletion, AModuleOrUnitReportsAnUnassignedOutput) {
  for (const auto& placed : InEveryDeclarationPlace(kCompletionPlace, "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "(a, o = 1) or b", kUnassignedAtMatch);
    }
  }
}

TEST(LocalFormalMatchCompletion, DISABLED_EveryOtherPlaceReportsIt) {
  for (const auto& placed : InEveryDeclarationPlace(kCompletionPlace, "")) {
    if (!InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "(a, o = 1) or b", kUnassignedAtMatch);
    }
  }
}

TEST(LocalFormalMatchCompletion, EveryPlaceAcceptsAnAssignedOutput) {
  for (const auto& placed : InEveryDeclarationPlace(kCompletionPlace, "")) {
    ExpectFormAccepted(placed.source, "(a, o = 1) or (b, o = 2)");
  }
}

}  // namespace
