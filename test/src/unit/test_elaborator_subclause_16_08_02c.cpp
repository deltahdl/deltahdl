#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "helpers_sequence_formal_bench.h"

using namespace delta;

namespace {

constexpr FormalReport kOutward = {
    .message = "shall be a reference to a local variable in scope",
    .subclause = "16.8.2"};

const char kOutwardTakers[] =
    "sequence si(local inout int lv); (a, lv += 1); endsequence\n"
    "  sequence so(local output int lv); (a, lv = 1); endsequence\n"
    "  int g;\n"
    "  @@";

std::string Taking(const char* taker, const std::string& use) {
  std::string out = use;
  for (std::size_t at = out.find("X("); at != std::string::npos;
       at = out.find("X(", at + 1)) {
    out.replace(at, 1, taker);
  }
  return out;
}

const char* const kNotALocal[] = {
    "property p; X(g) |-> a; endproperty",
    "assert property (@(posedge clk) X(g));",
    "sequence t; int q; (1, q = 0) ##1 X(q[0]); endsequence",
    "sequence t; int v; (1, v = 0) ##1 X((v)); endsequence"};

const char* const kALocal[] = {
    "property p; int v; (1, v = 0) ##1 X(v) |-> a; endproperty",
    "sequence t(local inout int w); X(w); endsequence",
    "sequence t; int q; (1, q = 0) ##1 X(q); endsequence",
    "sequence t; int v; (1, v = 0) ##1 X(v); endsequence"};

TEST(LocalFormalOutwardActual, ANonLocalActualIsReported) {
  for (const char* taker : {"si", "so"}) {
    for (const char* use : {kNotALocal[0], kNotALocal[1]}) {
      ExpectReportedAs(FormalBench(kOutwardTakers), Taking(taker, use),
                       kOutward);
    }
  }
}

TEST(LocalFormalOutwardActual, ASelectOfALocalIsReported) {
  for (const char* taker : {"si", "so"}) {
    ExpectReportedAs(FormalBench(kOutwardTakers), Taking(taker, kNotALocal[2]),
                     kOutward);
  }
}

TEST(LocalFormalOutwardActual, DISABLED_AParenthesizedLocalIsReported) {
  for (const char* taker : {"si", "so"}) {
    ExpectReportedAs(FormalBench(kOutwardTakers), Taking(taker, kNotALocal[3]),
                     kOutward);
  }
}

TEST(LocalFormalOutwardActual, AWholeLocalIsAccepted) {
  for (const char* taker : {"si", "so"}) {
    for (const char* use : kALocal) {
      ExpectFormAccepted(FormalBench(kOutwardTakers), Taking(taker, use));
    }
  }
}

const char kUnitTakers[] =
    "int g;\n"
    "  sequence si(local inout int lv); (a, lv += 1); endsequence\n"
    "  sequence so(local output int lv); (a, lv = 1); endsequence\n"
    "  sequence t; int v; (1, v = 0) ##1 @@; endsequence";

TEST(LocalFormalOutwardActual, AModuleOrUnitVariableIsReported) {
  for (const auto& placed : InEveryDeclarationPlace(kUnitTakers, "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "si(g)", kOutward);
      ExpectReportedAs(placed.source, "so(g)", kOutward);
    }
  }
}

TEST(LocalFormalOutwardActual, DISABLED_APackageOrUnitVariableIsReported) {
  for (const auto& placed : InEveryDeclarationPlace(kUnitTakers, "")) {
    if (placed.place == "package" || placed.place == "compilation unit") {
      ExpectReportedAs(placed.source, "si(g)", kOutward);
      ExpectReportedAs(placed.source, "so(g)", kOutward);
    }
  }
}

TEST(LocalFormalOutwardActual, EveryPlaceAcceptsItsOwnLocal) {
  for (const auto& placed : InEveryDeclarationPlace(kUnitTakers, "")) {
    if (placed.place == "clocking block") continue;
    ExpectFormAccepted(placed.source, "si(v)");
    ExpectFormAccepted(placed.source, "so(v)");
  }
}

constexpr FormalReport kCast = {.message = "is not cast compatible with",
                                .subclause = "16.8.2"};

const char kCastTypes[] =
    "typedef struct { int x; int y; } d_t;\n"
    "class k; int v; endclass\n"
    "typedef enum {E0, E1} e_t;\n";

const char kCastTakers[] =
    "sequence si(local inout int lv); (a, lv += 1); endsequence\n"
    "  sequence so(local output int lv); (a, lv = 1); endsequence\n"
    "  sequence sl(local inout longint lv); (a, lv += 1); endsequence\n"
    "  sequence slo(local output longint lv); (a, lv = 1); endsequence\n"
    "  sequence sn(local inout int n [2]); (a, n[0] = 1); endsequence\n"
    "  sequence t;\n"
    "    int q2 [2] = '{1, 2}; int q3 [3] = '{1, 2, 3}; d_t d = '{1, 2};\n"
    "    k h = null; byte y = 1; real r = 1.0; e_t e = E0; int v = 1;\n"
    "    @@;\n"
    "  endsequence";

std::string CastBench() { return FormalBench(kCastTakers, kCastTypes); }

TEST(LocalFormalOutwardActual, DISABLED_AnIncompatibleLocalIsReported) {
  for (const char* use : {"si(q2)", "so(q2)", "si(d)", "so(d)", "si(h)",
                          "so(h)", "sn(q3)", "sn(v)"}) {
    ExpectReportedAs(CastBench(), use, kCast);
  }
}

TEST(LocalFormalOutwardActual, ACompatibleLocalIsAccepted) {
  for (const char* use :
       {"sl(q2)", "slo(q2)", "sl(d)", "slo(d)", "sn(q2)", "si(y)", "so(y)",
        "si(r)", "so(r)", "si(e)", "so(e)"}) {
    ExpectFormAccepted(CastBench(), use);
  }
}

TEST(LocalFormalOutwardActual, DISABLED_AnIncompatiblePropertyOrFormalIsRep) {
  const std::string kTakers =
      "sequence si(local inout int lv); (a, lv += 1); endsequence\n  @@";
  ExpectReportedAs(FormalBench(kTakers),
                   "property p; int q [2] = '{1, 2}; si(q) |-> a; endproperty",
                   kCast);
  ExpectReportedAs(FormalBench(kTakers),
                   "sequence t(local input int w [2]); si(w); endsequence",
                   kCast);
}

TEST(LocalFormalOutwardActual, DISABLED_EveryPlaceReportsAnIncompatibleLocal) {
  for (const auto& placed : InEveryDeclarationPlace(
           "sequence si(local inout int lv); (a, lv += 1); endsequence\n"
           "  sequence t; int q [2] = '{1, 2}; @@; endsequence",
           "")) {
    ExpectReportedAs(placed.source, "si(q)", kCast);
  }
}

constexpr FormalReport kEmpty = {.message = "admits an empty match",
                                 .subclause = "16.8.2",
                                 .at = "sequence t"};

std::string EmptyBench(const std::string& formal) {
  return FormalBench("sequence s(" + formal +
                     " o); @@; endsequence\n"
                     "  sequence t; int v; (1, v = 0) ##1 s(v) ##1 b; "
                     "endsequence");
}

TEST(LocalFormalEmptyMatch, EveryBodyAdmittingAnEmptyMatchIsReported) {
  for (const char* body :
       {"(a, o += 1)[*0]", "(a, o += 1) or b[*0]", "(a, o += 1)[*]"}) {
    ExpectReportedAs(EmptyBench("local inout int"), body, kEmpty);
  }
  ExpectReportedAs(EmptyBench("local output int"), "(a, o = 1)[*0:1]", kEmpty);
}

TEST(LocalFormalEmptyMatch, ABodyWithNoEmptyMatchIsAccepted) {
  ExpectFormAccepted(EmptyBench("local inout int"), "a ##1 (b, o += 1)[*0:1]");
  ExpectFormAccepted(EmptyBench("local inout int"), "(a, o += 1) ##0 b[*0]");
  ExpectFormAccepted(EmptyBench("local output int"), "(a, o = 1) ##1 b");
  ExpectFormAccepted(EmptyBench("local input int"), "(a ##0 (o == 1))[*0:1]");
  ExpectFormAccepted(EmptyBench("int"), "(a ##0 (o == 1))[*0:1]");
}

TEST(LocalFormalEmptyMatch, AnInstanceReachingAnEmptyMatchIsReportedTwice) {
  const std::string kNested = FormalBench(
      "sequence s_or(local inout int o); (a, o += 1) or b[*0]; endsequence\n"
      "  sequence s_in(local inout int o); s_or(o); endsequence\n"
      "  sequence t; int v; (1, v = 0) ##1 s_in(v) ##1 b; endsequence");
  ExpectReportedAs(kNested, "", kEmpty);
  ExpectReportedAs(kNested, "",
                   {.message = kEmpty.message,
                    .subclause = "16.8.2",
                    .at = "sequence s_in"});
}

TEST(LocalFormalEmptyMatch, AnInstanceInAPropertyIsReported) {
  ExpectReportedAs(
      FormalBench("sequence s(local inout int o); (a, o += 1)[*0:1]; "
                  "endsequence\n"
                  "  property t; int v; (1, v = 0) ##1 s(v) |-> (v == 1); "
                  "endproperty"),
      "",
      {.message = kEmpty.message, .subclause = "16.8.2", .at = "property t"});
}

const char kEmptyPair[] =
    "sequence s(local inout int o); @@; endsequence\n"
    "  sequence t; int v; (1, v = 0) ##1 s(v) ##1 b; endsequence";

TEST(LocalFormalEmptyMatch, AModuleOrUnitReportsAnEmptyMatch) {
  for (const auto& placed : InEveryDeclarationPlace(kEmptyPair, "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "(a, o += 1)[*0:1]", kEmpty);
    }
  }
}

TEST(LocalFormalEmptyMatch, DISABLED_EveryOtherPlaceReportsAnEmptyMatch) {
  for (const auto& placed : InEveryDeclarationPlace(kEmptyPair, "")) {
    if (!InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "(a, o += 1)[*0:1]", kEmpty);
    }
  }
}

TEST(LocalFormalEmptyMatch, EveryPlaceAcceptsANonEmptyBody) {
  for (const auto& placed : InEveryDeclarationPlace(kEmptyPair, "")) {
    ExpectFormAccepted(placed.source, "a ##1 (b, o += 1)[*0:1]");
  }
}

const char kEmptyPackage[] =
    "package pk;\n"
    "  bit a, b;\n"
    "  sequence s(local inout int o); @@; endsequence\n"
    "  sequence t; int v; (1, v = 0) ##1 s(v) ##1 b; endsequence\n"
    "endpackage\n";

const char* const kOutsideUses[] = {
    "sequence tm; int v; (1, v = 0) ##1 pk::s(v) ##1 b; endsequence",
    ("import pk::*;\n  sequence tm; int v; (1, v = 0) ##1 s(v) ##1 b; "
     "endsequence"),
    "sequence w; pk::t; endsequence"};

TEST(LocalFormalEmptyMatch, DISABLED_AnOutsideInstanceIsReported) {
  for (const char* use : {kOutsideUses[0], kOutsideUses[1]}) {
    ExpectReportedAs(FormalBench(use, kEmptyPackage), "(a, o += 1)[*0:1]",
                     {.message = kEmpty.message,
                      .subclause = "16.8.2",
                      .at = "sequence tm"});
  }
  ExpectReportedAs(
      FormalBench(kOutsideUses[2], kEmptyPackage), "(a, o += 1)[*0:1]",
      {.message = kEmpty.message, .subclause = "16.8.2", .at = "  sequence t"});
  ExpectReportedAs(
      FormalBench("sequence t; int v; (1, v = 0) ##1 s(v) ##1 b; endsequence",
                  "bit a, b;\nsequence s(local inout int o); @@; "
                  "endsequence\n"),
      "(a, o += 1)[*0:1]", kEmpty);
}

TEST(LocalFormalEmptyMatch, AnOutsideInstanceOfANonEmptyBodyIsAccepted) {
  for (const char* use : kOutsideUses) {
    ExpectFormAccepted(FormalBench(use, kEmptyPackage),
                       "a ##1 (b, o += 1)[*0:1]");
  }
}

constexpr FormalReport kTwice = {
    .message = "is the actual of two inout or output local variable formals",
    .subclause = "16.8.2"};

const char kPairTakers[] =
    "sequence soi(local output int x, local inout int y); (a, x = 1, y += 1); "
    "endsequence\n"
    "  sequence soo(local output int x, y); (a, x = 1, y = 2); endsequence\n"
    "  sequence sii(local inout int x, local inout int y); (a, x += 1, y += "
    "1); "
    "endsequence\n"
    "  sequence sio(local input int x, local output int y); (a, y = x); "
    "endsequence\n"
    "  @@";

const char* const kSameLocalTwice[] = {
    "sequence t; int v = 0; soi(v, v); endsequence",
    "sequence t; int v = 0; soo(v, v); endsequence",
    "sequence t; int v = 0; sii(v, v); endsequence",
    "property p; int v = 0; soi(v, v) |-> a; endproperty",
    "sequence t(local inout int w); sii(w, w); endsequence",
    "sequence t; int v = 0; soo(.y(v), .x(v)); endsequence"};

TEST(LocalFormalOutwardActual, ALocalBoundToTwoOutwardFormalsIsReported) {
  for (const char* use : kSameLocalTwice) {
    ExpectReportedAs(FormalBench(kPairTakers), use, kTwice);
  }
}

TEST(LocalFormalOutwardActual, DistinctLocalsOrAnInputBindingAreAccepted) {
  for (const char* use :
       {"sequence t; int v = 0, w = 0; soi(v, w); endsequence",
        "sequence t; int v, w; soo(v, w); endsequence",
        "sequence t; int v = 0, w = 0; sii(v, w); endsequence",
        "sequence t; int v = 0; sio(v, v); endsequence"}) {
    ExpectFormAccepted(FormalBench(kPairTakers), use);
  }
}

const char kPairPlace[] =
    "sequence soo(local output int x, y); (a, x = 1, y = 2); endsequence\n"
    "  sequence t; int v; @@; endsequence";

constexpr FormalReport kTwiceInT = {
    .message = kTwice.message, .subclause = "16.8.2", .at = "sequence t"};

TEST(LocalFormalOutwardActual, AModuleOrUnitReportsALocalBoundTwice) {
  for (const auto& placed : InEveryDeclarationPlace(kPairPlace, "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "soo(v, v)", kTwiceInT);
    }
  }
}

TEST(LocalFormalOutwardActual,
     DISABLED_EveryOtherPlaceReportsALocalBoundTwice) {
  for (const auto& placed : InEveryDeclarationPlace(kPairPlace, "")) {
    if (!InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "soo(v, v)", kTwiceInT);
    }
  }
}

TEST(LocalFormalOutwardActual, EveryPlaceAcceptsTwoDistinctLocals) {
  for (const auto& placed : InEveryDeclarationPlace(
           "sequence soo(local output int x, y); (a, x = 1, y = 2); "
           "endsequence\n  sequence t; int v, w; @@; endsequence",
           "")) {
    ExpectFormAccepted(placed.source, "soo(v, w)");
  }
}

}  // namespace
