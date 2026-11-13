#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_sequence_formal_bench.h"

using namespace delta;

namespace {

constexpr FormalReport kMethod = {
    .message = "may not be applied to an instance of", .subclause = "16.8.2"};

const char kMethodTakers[] =
    "sequence si(local input int x); @(posedge clk) a ##1 (x == 1); "
    "endsequence\n"
    "  sequence sio(local inout int y); @(posedge clk) (a, y += 1); "
    "endsequence\n"
    "  sequence sinf(local int x); @(posedge clk) a ##1 (x == 1); endsequence\n"
    "  sequence sdef(local input int x = 1); @(posedge clk) a ##1 (x == 1); "
    "endsequence\n"
    "  sequence smix(local output int w, local input int x);\n"
    "    @(posedge clk) (a, w = x);\n"
    "  endsequence\n"
    "  sequence snl(local input int x, int z); @(posedge clk) a ##1 (x == z); "
    "endsequence\n"
    "  sequence sz(int z, local int x); @(posedge clk) a ##1 (x == z); "
    "endsequence\n"
    "  sequence s3(local output int w); @(posedge clk) (a, w = 1); "
    "endsequence\n"
    "  sequence su(z, int q); @(posedge clk) a ##1 (z == q); endsequence\n"
    "  sequence so2(local output int o, p); @(posedge clk) (a, o = 1, p = 2); "
    "endsequence\n"
    "  @@";

std::string MethodBench() { return FormalBench(kMethodTakers); }

const char* const kTriggeredInAssertions[] = {
    "sequence u; @(posedge clk) b ##1 si(1).triggered; endsequence",
    ("sequence u; int v; @(posedge clk) (b, v = 0) ##1 sio(v).triggered; "
     "endsequence"),
    "property u; @(posedge clk) b |-> si(1).triggered; endproperty",
    ("property u; int v; @(posedge clk) (b, v = 0) |-> sio(v).triggered; "
     "endproperty"),
    "assert property (@(posedge clk) b |-> si(1).triggered);"};

TEST(LocalFormalMethod, TriggeredInAnAssertionIsReported) {
  for (const char* use : kTriggeredInAssertions) {
    ExpectReportedAs(MethodBench(), use, kMethod);
  }
}

const char* const kTriggeredProcedurally[] = {
    "initial if (si(1).triggered) $display(\"t\");",
    "function bit f(); return si(1).triggered; endfunction",
    "task tk; wait (si(1).triggered); endtask",
    "initial wait (sinf(1).triggered);",
    "initial wait (sdef().triggered);",
    "initial wait (snl(1, 2).triggered);",
    "initial wait (sz(2, 1).triggered);"};

TEST(LocalFormalMethod, TriggeredProcedurallyIsReported) {
  for (const char* use : kTriggeredProcedurally) {
    ExpectReportedAs(MethodBench(), use, kMethod);
  }
}

const char* const kMatched[] = {
    "sequence u; @(posedge clk) b ##1 si(1).matched; endsequence",
    ("sequence u; int v; @(posedge clk) (b, v = 0) ##1 sio(v).matched; "
     "endsequence"),
    "property u; @(posedge clk) b |-> si(1).matched; endproperty",
    "assert property (@(posedge clk) b |-> si(1).matched);",
    "sequence u; @(posedge clk) b ##1 sdef().matched; endsequence",
    "sequence u; int w; @(posedge clk) b ##1 smix(w, 1).matched; endsequence"};

TEST(LocalFormalMethod, MatchedIsReported) {
  for (const char* use : kMatched) {
    ExpectReportedAs(MethodBench(), use, kMethod);
  }
}

const char* const kAllowedMethods[] = {
    "sequence u; int w; @(posedge clk) b ##1 s3(w).triggered; endsequence",
    "sequence u; int w; @(posedge clk) b ##1 s3(w).matched; endsequence",
    "initial wait (su(1, 2).triggered);",
    "sequence u; @(posedge clk) b ##1 su(1, 2).matched; endsequence",
    ("sequence u; int w1, w2; @(posedge clk) b ##1 so2(w1, w2).matched; "
     "endsequence")};

TEST(LocalFormalMethod, AMethodOfAnInstanceWithNoInputLocalIsAccepted) {
  for (const char* use : kAllowedMethods) {
    ExpectFormAccepted(MethodBench(), use);
  }
}

TEST(LocalFormalMethod, AnOutputOnlyInstanceInProceduralCodeIsNotCited) {
  ExpectReportedAs(MethodBench(), "int w;\n  initial wait (s3(w).triggered);",
                   {.message = kMethod.message,
                    .subclause = "16.8.2",
                    .at = "initial wait",
                    .times = 0});
}

const char kMethodPair[] =
    "sequence s(local input int x); @(posedge clk) a ##1 (x == 1); "
    "endsequence\n"
    "  sequence so(local output int w); @(posedge clk) (a, w = 1); "
    "endsequence\n"
    "  sequence u; int w; @(posedge clk) b ##1 @@; endsequence";

constexpr FormalReport kMethodInU = {
    .message = kMethod.message, .subclause = "16.8.2", .at = "sequence u"};

TEST(LocalFormalMethod, AModuleOrUnitReportsAMethod) {
  for (const auto& placed : InEveryDeclarationPlace(kMethodPair, "")) {
    if (InAModuleOrUnit(placed)) {
      ExpectReportedAs(placed.source, "s(1).matched", kMethodInU);
      ExpectReportedAs(placed.source, "s(1).triggered", kMethodInU);
    }
  }
}

TEST(LocalFormalMethod, DISABLED_EveryOtherPlaceReportsAMethod) {
  for (const auto& placed : InEveryDeclarationPlace(kMethodPair, "")) {
    if (!InAModuleOrUnit(placed) && placed.place != "clocking block") {
      ExpectReportedAs(placed.source, "s(1).matched", kMethodInU);
      ExpectReportedAs(placed.source, "s(1).triggered", kMethodInU);
    }
  }
}

TEST(LocalFormalMethod, EveryPlaceAcceptsAMethodOfAnOutputOnlyInstance) {
  for (const auto& placed : InEveryDeclarationPlace(kMethodPair, "")) {
    if (placed.place == "clocking block") continue;
    ExpectFormAccepted(placed.source, "so(w).triggered");
    ExpectFormAccepted(placed.source, "so(w).matched");
  }
}

const char kMethodPackage[] =
    "package pk;\n"
    "  bit clk, a;\n"
    "  sequence s(local input int x); @(posedge clk) a ##1 (x == 1); "
    "endsequence\n"
    "  sequence su(int x); @(posedge clk) a ##1 (x == 1); endsequence\n"
    "endpackage\n";

const char kMethodInterface[] =
    "interface ifc(input logic clk, a);\n"
    "  sequence s(local input int x); @(posedge clk) a ##1 (x == 1); "
    "endsequence\n"
    "  sequence su(int x); @(posedge clk) a ##1 (x == 1); endsequence\n"
    "endinterface\n";

const char kMethodGenerate[] =
    "if (1) begin : g\n"
    "    sequence s(local input int x); @(posedge clk) a ##1 (x == 1); "
    "endsequence\n"
    "    sequence su(int x); @(posedge clk) a ##1 (x == 1); endsequence\n"
    "  end\n  ";

struct MethodSite {
  std::string outside;
  std::string items;
};

std::vector<MethodSite> MethodSites() {
  return {
      {"", std::string(kMethodGenerate) + "initial wait (g.@@(1).triggered);"},
      {kMethodPackage, "initial wait (pk::@@(1).triggered);"},
      {kMethodPackage, "import pk::*;\n  initial wait (@@(1).triggered);"},
      {std::string("bit clk, a;\n") +
           "sequence s(local input int x); @(posedge clk) a ##1 (x == 1); "
           "endsequence\n"
           "sequence su(int x); @(posedge clk) a ##1 (x == 1); endsequence\n",
       "initial wait (@@(1).triggered);"},
      {kMethodInterface,
       "ifc i(clk, a);\n  initial wait (i.@@(1).triggered);"}};
}

TEST(LocalFormalMethod, DISABLED_AMethodReachingAnotherScopeIsReported) {
  for (const auto& site : MethodSites()) {
    ExpectReportedAs(FormalBench(site.items, site.outside), "s", kMethod);
  }
}

TEST(LocalFormalMethod, AMethodReachingAnotherScopeWithNoLocalIsAccepted) {
  for (const auto& site : MethodSites()) {
    ExpectFormAccepted(FormalBench(site.items, site.outside), "su");
  }
}

constexpr FormalReport kInputCast = {.message = "is not cast compatible with",
                                     .subclause = "16.8.2"};

const char kInputCastTakers[] =
    "sequence sin(local input int k); a ##1 (k != 0); endsequence\n"
    "  sequence sio(local inout int k); (a, k += 1); endsequence\n"
    "  property pin(local input int k); a |-> k != 0; endproperty\n"
    "  int arr [2]; byte b4 [4]; d_t d;\n"
    "  @@";

std::string InputCastBench() {
  return FormalBench(kInputCastTakers,
                     "typedef struct { int x; int y; } d_t;\n");
}

const char* const kIncompatibleInputs[] = {
    "cover property (@(posedge clk) sin(arr));",
    "cover property (@(posedge clk) sin(d));",
    "sequence t; int q [2] = '{1, 2}; sio(q); endsequence",
    "assert property (@(posedge clk) pin(arr));",
    "sequence sdef(local input int k = arr); a ##1 (k != 0); endsequence"};

TEST(LocalFormalInitialization, DISABLED_AnIncompatibleActualIsReported) {
  for (const char* use : kIncompatibleInputs) {
    ExpectReportedAs(InputCastBench(), use, kInputCast);
  }
}

TEST(LocalFormalInitialization, ACompatibleActualIsAccepted) {
  for (const char* use : {"cover property (@(posedge clk) sin(b4));",
                          "cover property (@(posedge clk) sin(8'd3));",
                          "cover property (@(posedge clk) sin(64'd3));",
                          "assert property (@(posedge clk) pin(b4));"}) {
    ExpectFormAccepted(InputCastBench(), use);
  }
}

}  // namespace
