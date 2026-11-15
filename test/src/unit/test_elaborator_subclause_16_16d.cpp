#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

constexpr const char* kReport =
    "is not clocked on the block's clocking event alone";

struct Place {
  const char* open;
  const char* close;
};

constexpr Place kModule{"module m;\n", "endmodule\n"};

std::string Source(const std::string& outside, const std::string& event,
                   const std::string& inside, const Place& place = kModule,
                   const char* block = "clocking cb ") {
  return std::string(place.open) + "  bit clk, clk2, b, en, rst;\n" + outside +
         "  " + block + event + ";\n" + inside + "  endclocking\n" +
         place.close;
}

std::string InProperty(const std::string& body) {
  return "    property t;\n      " + body + ";\n    endproperty\n";
}

std::string InSequence(const std::string& body) {
  return "    sequence t;\n      " + body + ";\n    endsequence\n";
}

void ExpectReports(size_t expected, const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  size_t count = 0;
  std::string all;
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    all += std::to_string(diag.loc.line) + ": " + diag.message + "\n";
    if (diag.severity == DiagSeverity::kError &&
        diag.message.find(kReport) != std::string::npos &&
        diag.subclause == "16.16") {
      ++count;
    }
  }
  EXPECT_EQ(count, expected) << src << all;
}

std::string Seq(const char* name, const std::string& body) {
  return "  sequence " + std::string(name) + ";\n    " + body +
         ";\n  endsequence\n";
}

TEST(OutsideInstanceInBlock, ASequenceOnTheBlocksEventOrNoneIsAccepted) {
  ExpectReports(0, Source(Seq("s", "@(posedge clk) b"), "@(posedge clk)",
                          InProperty("s")));
  ExpectReports(0,
                Source(Seq("s", "b ##1 b"), "@(posedge clk)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, AMulticlockedSequenceIsReported) {
  ExpectReports(1, Source(Seq("s", "@(posedge clk) b ##1 @(negedge clk) b"),
                          "@(posedge clk)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, ASequenceOnOneIdenticalClockIsAccepted) {
  ExpectReports(0, Source(Seq("s", "@(posedge clk) b ##1 b"), "@(posedge clk)",
                          InProperty("s")));
}

TEST(OutsideInstanceInBlock, AClockOnAnEqualSignalIsNotIdentical) {
  ExpectReports(1,
                Source("  assign clk2 = clk;\n" + Seq("s", "@(posedge clk2) b"),
                       "@(posedge clk)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, AClockOnTheSameSignalIsIdentical) {
  ExpectReports(0,
                Source("  assign clk2 = clk;\n" + Seq("s", "@(posedge clk) b"),
                       "@(posedge clk)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, DISABLED_AnIffGuardMakesTheEventsDiffer) {
  ExpectReports(1, Source(Seq("s", "@(posedge clk iff en) b"), "@(posedge clk)",
                          InProperty("s")));
  ExpectReports(1, Source(Seq("s", "@(posedge clk) b"), "@(posedge clk iff en)",
                          InProperty("s")));
}

TEST(OutsideInstanceInBlock, TheSameIffGuardIsIdentical) {
  ExpectReports(0, Source(Seq("s", "@(posedge clk iff en) b"),
                          "@(posedge clk iff en)", InProperty("s")));
}

TEST(OutsideInstanceInBlock,
     DISABLED_AnotherEventThanAnOrBlockEventIsReported) {
  ExpectReports(1, Source(Seq("s", "@(negedge clk) b"),
                          "@(posedge clk or negedge rst)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, TheSameOrEventOrNoneIsAccepted) {
  ExpectReports(0, Source(Seq("s", "@(posedge clk or negedge rst) b"),
                          "@(posedge clk or negedge rst)", InProperty("s")));
  ExpectReports(0, Source(Seq("s", "b"), "@(posedge clk or negedge rst)",
                          InProperty("s")));
}

TEST(OutsideInstanceInBlock, AnEdgeAgainstAnEdgelessBlockEventIsReported) {
  ExpectReports(
      1, Source(Seq("s", "@(negedge clk) b"), "@(clk)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, TheSameEdgelessEventIsAccepted) {
  ExpectReports(0, Source(Seq("s", "@(clk) b"), "@(clk)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, AnEdgeAgainstANamedEventBlockIsReported) {
  ExpectReports(1, Source("  event e;\n" + Seq("s", "@(negedge clk) b"), "@e",
                          InProperty("s")));
}

TEST(OutsideInstanceInBlock, TheSameNamedEventIsAccepted) {
  ExpectReports(
      0, Source("  event e;\n" + Seq("s", "@(e) b"), "@e", InProperty("s")));
}

TEST(OutsideInstanceInBlock, DISABLED_ANestedInstanceOnAnotherClockIsReported) {
  ExpectReports(1, Source(Seq("sn", "@(negedge clk) b") + Seq("s", "sn"),
                          "@(posedge clk)", InProperty("s")));
}

TEST(OutsideInstanceInBlock, ANestedInstanceOnTheBlocksClockIsAccepted) {
  ExpectReports(0, Source(Seq("sp", "@(posedge clk) b") + Seq("s", "sp"),
                          "@(posedge clk)", InProperty("s")));
}

constexpr const char* kEventFormal =
    "  sequence se(ev);\n    @(ev) b;\n  endsequence\n";

TEST(OutsideInstanceInBlock, AnEventArgumentOnAnotherClockIsReported) {
  ExpectReports(
      1, Source(kEventFormal, "@(posedge clk)", InProperty("se(negedge clk)")));
}

TEST(OutsideInstanceInBlock,
     DISABLED_AnEventArgumentOnTheBlocksClockIsAccepted) {
  ExpectReports(
      0, Source(kEventFormal, "@(posedge clk)", InProperty("se(posedge clk)")));
}

constexpr const char* kWithArguments =
    "  property pn(x);\n    @(negedge clk) x;\n  endproperty\n"
    "  property pp(x);\n    @(posedge clk) x;\n  endproperty\n"
    "  sequence sn(x);\n    @(negedge clk) x;\n  endsequence\n";

TEST(OutsideInstanceInBlock, DISABLED_AnInstanceWithArgumentsIsReportedOnce) {
  ExpectReports(1,
                Source(kWithArguments, "@(posedge clk)", InProperty("pn(b)")));
  ExpectReports(1,
                Source(kWithArguments, "@(posedge clk)", InProperty("sn(b)")));
  ExpectReports(1,
                Source(kWithArguments, "@(posedge clk)", InSequence("sn(b)")));
}

TEST(OutsideInstanceInBlock, AnInstanceWithArgumentsOnTheBlocksClock) {
  ExpectReports(0,
                Source(kWithArguments, "@(posedge clk)", InProperty("pp(b)")));
}

constexpr const char* kClockKinds =
    "  sequence sneg;\n    @(negedge clk) b;\n  endsequence\n"
    "  sequence spos;\n    @(posedge clk) b;\n  endsequence\n"
    "  sequence snone;\n    b;\n  endsequence\n"
    "  sequence smulti;\n    @(posedge clk) b ##1 @(negedge clk) b;\n"
    "  endsequence\n";

TEST(OutsideInstanceInBlock, AnInstanceInABlocksSequenceIsJudged) {
  ExpectReports(
      1, Source(kClockKinds, "@(posedge clk)", InSequence("sneg ##1 b")));
  ExpectReports(
      1, Source(kClockKinds, "@(posedge clk)", InSequence("smulti ##1 b")));
}

TEST(OutsideInstanceInBlock, AnAgreeingInstanceInABlocksSequenceIsAccepted) {
  ExpectReports(
      0, Source(kClockKinds, "@(posedge clk)", InSequence("spos ##1 b")));
  ExpectReports(
      0, Source(kClockKinds, "@(posedge clk)", InSequence("snone ##1 b")));
}

constexpr const char* kPropertyKinds =
    "  property qneg;\n    @(negedge clk) b;\n  endproperty\n"
    "  property qpos;\n    @(posedge clk) b;\n  endproperty\n";

TEST(OutsideInstanceInBlock, ANonLeadingInstanceOnAnotherClockIsReported) {
  for (const char* body : {"b ##1 sneg", "b |=> qneg", "not sneg"}) {
    ExpectReports(1, Source(std::string(kClockKinds) + kPropertyKinds,
                            "@(posedge clk)", InProperty(body)));
  }
}

TEST(OutsideInstanceInBlock, ANonLeadingInstanceOnTheBlocksClockIsAccepted) {
  for (const char* body : {"b ##1 spos", "b |=> qpos", "not spos"}) {
    ExpectReports(0, Source(std::string(kClockKinds) + kPropertyKinds,
                            "@(posedge clk)", InProperty(body)));
  }
}

TEST(OutsideInstanceInBlock, TheClausesQ4IsAccepted) {
  ExpectReports(
      0, Source("  bit c;\n"
                "  property q1;\n    $rose(b) |-> ##[1:5] b;\n  endproperty\n"
                "  property q2;\n    @(posedge clk) q1;\n  endproperty\n",
                "posedge_clk @(posedge clk)", InProperty("$fell(c) |=> q2"),
                kModule, "default clocking "));
}

constexpr const char* kPackage =
    "package p;\n"
    "  bit pclk, pb;\n"
    "  sequence sneg;\n    @(negedge pclk) pb;\n  endsequence\n"
    "  sequence spos;\n    @(posedge pclk) pb;\n  endsequence\n"
    "endpackage\n";

TEST(OutsideInstanceInBlock,
     DISABLED_APackageSequenceOnAnotherClockIsReported) {
  ExpectReports(1, kPackage + Source("  import p::*;\n", "@(posedge pclk)",
                                     InProperty("p::sneg")));
  ExpectReports(1, kPackage + Source("  import p::*;\n", "@(posedge pclk)",
                                     InProperty("sneg")));
}

TEST(OutsideInstanceInBlock, APackageSequenceOnTheBlocksClockIsAccepted) {
  ExpectReports(0, kPackage + Source("  import p::*;\n", "@(posedge pclk)",
                                     InProperty("p::spos")));
  ExpectReports(0, kPackage + Source("  import p::*;\n", "@(posedge pclk)",
                                     InProperty("spos")));
}

constexpr const char* kUnit =
    "bit uclk, ub;\n"
    "sequence uneg;\n  @(negedge uclk) ub;\nendsequence\n"
    "sequence upos;\n  @(posedge uclk) ub;\nendsequence\n";

TEST(OutsideInstanceInBlock, DISABLED_AUnitSequenceOnAnotherClockIsReported) {
  ExpectReports(1, kUnit + Source("", "@(posedge uclk)", InProperty("uneg")));
}

TEST(OutsideInstanceInBlock, AUnitSequenceOnTheBlocksClockIsAccepted) {
  ExpectReports(0, kUnit + Source("", "@(posedge uclk)", InProperty("upos")));
}

constexpr const char* kTwoClocks =
    "  sequence sneg;\n    @(negedge clk) b;\n  endsequence\n"
    "  sequence spos;\n    @(posedge clk) b;\n  endsequence\n";

struct BlockPlace {
  Place place;
  const char* block;
};

constexpr BlockPlace kReportingPlaces[] = {
    {{"interface i;\n", "endinterface\nmodule top;\n  i ui();\nendmodule\n"},
     "clocking cb "},
    {{"program g;\n", "endprogram\n"}, "clocking cb "},
    {{"module m;\n  checker c;\n", "  endchecker\n  c uc();\nendmodule\n"},
     "clocking cb "},
    {kModule, "default clocking cb "},
};

constexpr BlockPlace kGeneratePlaces[] = {
    {{"module m;\n  if (1) begin : g\n", "  end\nendmodule\n"}, "clocking cb "},
    {{"module m;\n  for (genvar k = 0; k < 1; k++) begin : g\n",
      "  end\nendmodule\n"},
     "clocking cb "},
};

TEST(OutsideInstanceInBlock, EachDesignElementsBlockReportsAnotherClock) {
  for (const BlockPlace& where : kReportingPlaces) {
    ExpectReports(1, Source(kTwoClocks, "@(posedge clk)", InProperty("sneg"),
                            where.place, where.block));
  }
}

TEST(OutsideInstanceInBlock, DISABLED_AGenerateBlocksBlockReportsAnotherClock) {
  for (const BlockPlace& where : kGeneratePlaces) {
    ExpectReports(1, Source(kTwoClocks, "@(posedge clk)", InProperty("sneg"),
                            where.place, where.block));
  }
}

void ExpectOwnClockAccepted(const BlockPlace& where) {
  ExpectReports(0, Source(kTwoClocks, "@(posedge clk)", InProperty("spos"),
                          where.place, where.block));
}

TEST(OutsideInstanceInBlock, EachPlacesBlockAcceptsItsOwnClock) {
  for (const BlockPlace& where : kReportingPlaces) {
    ExpectOwnClockAccepted(where);
  }
  for (const BlockPlace& where : kGeneratePlaces) {
    ExpectOwnClockAccepted(where);
  }
}

}  // namespace
