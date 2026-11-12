#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_sequence_formal_bench.h"

using namespace delta;

namespace {

const char kCast[] = "is not cast compatible with";

const char kCastTypes[] =
    "typedef struct { byte x; byte y; byte z; } s24_t;\n"
    "typedef struct { longint x; } s64_t;\n"
    "typedef struct { int x; } s32_t;\n"
    "typedef struct { int x; int y; } d_t;\n"
    "class pub; int v; endclass\n"
    "class priv; local int v; endclass\n"
    "class prot; protected int v; endclass\n"
    "class kid extends priv; endclass\n";

const char kCastSequences[] =
    "int arr [2]; byte b4 [4]; int a33 [3][3]; int a6 [6]; int x23 [2][3];\n"
    "  int aa [int]; s24_t s24; s64_t s64; s32_t s32; d_t d; event ev;\n"
    "  real r; string str; pub hp; priv hv; prot hr; kid hk;\n"
    "  sequence si(int k); k != 0; endsequence\n"
    "  sequence sd(d_t k); k.x != 0; endsequence\n"
    "  sequence sr(real k); k != 0; endsequence\n"
    "  sequence ssr(shortreal k); k != 0; endsequence\n"
    "  sequence srt(realtime k); k != 0; endsequence\n"
    "  sequence sa(int k [2][3]); k[0][0] != 0; endsequence\n"
    "  sequence sq(int k [int]); k.num() != 0; endsequence\n"
    "  sequence se(event k); @(k) a; endsequence\n"
    "  property pi(int k); k != 0; endproperty\n"
    "  sequence outer(untyped v); si(v); endsequence\n";

std::string CastBench(const std::string& extra = "") {
  return FormalBench(std::string(kCastSequences) + extra +
                         "  cover property (@(posedge clk) @@);",
                     kCastTypes);
}

const char* const kIncompatible[] = {
    "si(arr)", "si(s24)", "si(s64)", "sd(5)",   "sr(arr)", "ssr(arr)",
    "srt(d)",  "si(hv)",  "si(hr)",  "si(hk)",  "si(ev)",  "sa(a33)",
    "sq(arr)", "pi(arr)", "sd(r)",   "sa(arr)", "si(d)"};

TEST(SequenceFormalCast, DISABLED_AnIncompatibleActualIsReported) {
  for (const char* actual : kIncompatible) {
    ExpectFormReported(CastBench(), actual, kCast);
  }
}

const char* const kCompatible[] = {
    "si(b4)",  "si(s32)", "sd(arr)", "sd(64'd5)", "sr(5)",    "si(r)",
    "sd(d)",   "sa(x23)", "sa(a6)",  "sq(aa)",    "se(ev)",   "si(hp)",
    "si(str)", "pi(b4)",  "ssr(3)",  "srt(r)",    "outer(b4)"};

TEST(SequenceFormalCast, ACompatibleActualIsAccepted) {
  for (const char* actual : kCompatible) {
    ExpectFormAccepted(CastBench(), actual);
  }
}

int CastReports(const std::string& src) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  int count = 0;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError && diag.subclause == "16.8.1" &&
        diag.message.find(kCast) != std::string::npos) {
      ++count;
    }
  }
  return count;
}

TEST(SequenceFormalCast, DISABLED_AnIncompatibleDefaultIsReported) {
  const std::string kDefault =
      "sequence sdef(int k = arr); k != 0; endsequence\n";
  EXPECT_EQ(CastReports(FilledForm(CastBench(kDefault), "sdef()")), 1);
  EXPECT_EQ(CastReports(FilledForm(CastBench(kDefault), "si(b4)")), 1);
}

TEST(SequenceFormalCast, ACompatibleDefaultIsAccepted) {
  ExpectFormAccepted(
      CastBench("sequence sdef(int k = b4); k != 0; endsequence\n"), "sdef()");
}

TEST(SequenceFormalCast, DISABLED_AnActualReachingThroughAnUntypedFormalIsRep) {
  EXPECT_EQ(CastReports(FilledForm(CastBench(), "outer(arr)")), 1);
}

const char kPlacedDecl[] =
    "int arr [2];\n"
    "  byte b4 [4];\n"
    "  sequence si(int k); k != 0; endsequence\n";

std::vector<PlacedSource> CastPlaces() {
  const std::string kDecl = kPlacedDecl;
  const std::string kUse = "  cover property (@(posedge clk) @@);";
  std::vector<PlacedSource> out;
  for (const char* kind : {"interface", "program", "checker"}) {
    out.push_back({kind, FormalBench("u_unit u(clk, a, b, c);",
                                     InUnit(kind, kDecl + kUse))});
  }
  out.push_back({"generate", FormalBench("if (1) begin : g\n  " + kDecl + kUse +
                                         "\n  end")});
  out.push_back(
      {"package",
       FormalBench("int arr [2];\n  byte b4 [4];\n"
                   "  cover property (@(posedge clk) pk::@@);",
                   "package pk;\n  sequence si(int k); k != 0; endsequence\n"
                   "endpackage\n")});
  out.push_back({"compilation unit",
                 FormalBench("int arr [2];\n  byte b4 [4];\n" + kUse,
                             "sequence si(int k); k != 0; endsequence\n")});
  out.push_back(
      {"always", FormalBench(kDecl + "  always begin\n"
                                     "    assert property (@(posedge clk) "
                                     "@@);\n"
                                     "  end")});
  out.push_back({"cover sequence",
                 FormalBench(kDecl + "  cover sequence (@(posedge clk) @@);")});
  return out;
}

TEST(SequenceFormalCast, EveryPlaceAcceptsACompatibleActual) {
  for (const auto& placed : CastPlaces()) {
    ExpectFormAccepted(placed.source, "si(b4)");
  }
}

TEST(SequenceFormalCast, DISABLED_EveryPlaceReportsAnIncompatibleActual) {
  for (const auto& placed : CastPlaces()) {
    ExpectFormReported(placed.source, "si(arr)", kCast);
  }
}

}  // namespace
