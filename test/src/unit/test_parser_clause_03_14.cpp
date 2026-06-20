#include "fixture_parser.h"
#include "parser/time_resolve.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, TimeUnitEnumValues) {
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kS), 0);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kMs), -3);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kUs), -6);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kNs), -9);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kPs), -12);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kFs), -15);
}

TEST(DesignBuildingBlockParsing, AllValidTimeUnitStringsAccepted) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("s", u));
  EXPECT_EQ(u, TimeUnit::kS);
  EXPECT_TRUE(ParseTimeUnitStr("ms", u));
  EXPECT_EQ(u, TimeUnit::kMs);
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_TRUE(ParseTimeUnitStr("ns", u));
  EXPECT_EQ(u, TimeUnit::kNs);
  EXPECT_TRUE(ParseTimeUnitStr("ps", u));
  EXPECT_EQ(u, TimeUnit::kPs);
  EXPECT_TRUE(ParseTimeUnitStr("fs", u));
  EXPECT_EQ(u, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, InvalidTimeUnitStringsRejected) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_FALSE(ParseTimeUnitStr("", u));
  EXPECT_FALSE(ParseTimeUnitStr("xs", u));
  EXPECT_FALSE(ParseTimeUnitStr("sec", u));
  EXPECT_FALSE(ParseTimeUnitStr("NS", u));
}

TEST(DesignBuildingBlockParsing, SlashPrecisionLessPreciseThanUnit) {
  EXPECT_FALSE(ParseOk("module m; timeunit 1ps / 1ns; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, SlashPrecisionValid) {
  EXPECT_TRUE(ParseOk("module m; timeunit 1ns / 1ps; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, SlashPrecisionEqualToUnit) {
  EXPECT_TRUE(ParseOk("module m; timeunit 1ns / 1ns; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, TimeScaleCarriesUnitAndPrecision) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 10;
  ts.precision = TimeUnit::kPs;
  ts.prec_magnitude = 100;
  EXPECT_EQ(ts.unit, TimeUnit::kNs);
  EXPECT_EQ(ts.precision, TimeUnit::kPs);
  EXPECT_NE(static_cast<int8_t>(ts.unit), static_cast<int8_t>(ts.precision));
}

TEST(DesignBuildingBlockParsing, ParserAcceptsMagnitudesOneTenHundred) {
  EXPECT_TRUE(ParseOk("module m; timeunit 1ns; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; timeunit 10ns; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; timeunit 100ns; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; timeprecision 1ps; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; timeprecision 10ps; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; timeprecision 100ps; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ParserRejectsOtherMagnitudesOnTimeunit) {
  EXPECT_FALSE(ParseOk("module m; timeunit 5ns; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; timeunit 50ns; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; timeunit 1000ns; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; timeunit 2ns; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ParserRejectsOtherMagnitudesOnTimeprecision) {
  EXPECT_FALSE(ParseOk("module m; timeprecision 5ps; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; timeprecision 200ps; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ParserRejectsBadMagnitudeInSlashPrecision) {
  EXPECT_FALSE(ParseOk("module m; timeunit 1ns / 5ps; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, RangeSpansHundredSecondsDownToOneFemtosecond) {
  EXPECT_TRUE(ParseOk("module m; timeunit 100s; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; timeunit 1fs; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MagnitudeAndUnitHelperRoundTrip) {
  int mag = 0;
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(TryParseTimeMagnitudeAndUnit("100ps", mag, u));
  EXPECT_EQ(mag, 100);
  EXPECT_EQ(u, TimeUnit::kPs);

  EXPECT_FALSE(TryParseTimeMagnitudeAndUnit("7ns", mag, u));
  EXPECT_FALSE(TryParseTimeMagnitudeAndUnit("ns", mag, u));
  EXPECT_FALSE(TryParseTimeMagnitudeAndUnit("1xy", mag, u));
}

TEST(DesignBuildingBlockParsing, ParsedModuleStoresBothUnitAndPrecision) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 100ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_unit_magnitude, 10);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
  EXPECT_EQ(mod->time_prec_magnitude, 100);
}

TEST(DesignBuildingBlockParsing, SlashPrecisionLongerByMagnitudeRejected) {
  EXPECT_FALSE(ParseOk("module m; timeunit 1ns / 10ns; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; timeunit 10ps / 100ps; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, SlashPrecisionFinerByMagnitudeAccepted) {
  EXPECT_TRUE(ParseOk("module m; timeunit 100ps / 1ps; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; timeunit 10ns / 1ns; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, EffectiveOrderOrdersMagnitudeAndUnit) {
  EXPECT_GT(EffectiveTimeOrder(TimeUnit::kNs, 100),
            EffectiveTimeOrder(TimeUnit::kNs, 1));
  EXPECT_GT(EffectiveTimeOrder(TimeUnit::kUs, 1),
            EffectiveTimeOrder(TimeUnit::kNs, 100));
  EXPECT_EQ(EffectiveTimeOrder(TimeUnit::kNs, 1),
            EffectiveTimeOrder(TimeUnit::kNs, 1));
}

}  // namespace
