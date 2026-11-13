#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "helpers_property_places.h"

namespace {

constexpr const char* kEdgeStimulus =
    "  assign a = tick inside {1, 2, 3};\n"
    "  initial begin b = 0; #2 b = 1; #10 b = 0; #5 b = 1; #15 b = 0; end\n";

constexpr PlacedProperty kJoinsToAnotherClock[] = {
    {"a ##1 @(negedge clk) b", {3, 1}, 3},
    {"a ##0 @(negedge clk) b", {3, 1}, 3},
    {"a ##1 @(clk) b", {3, 1}, 3},
    {"a ##0 @(clk) b", {2, 2}, 2}};

constexpr PlacedProperty kJoinsOnTheClockInForce[] = {
    {"a ##1 @(posedge clk) b", {1, 3}, 1},
    {"a ##0 @(posedge clk) b", {2, 2}, 2},
    {"a ##1 b", {1, 3}, 1},
    {"a && b", {2, 2}, 2}};

constexpr const char* kStaticPlaces[] = {
    "module",  "generate",        "interface",      "program",
    "checker", "module property", "module sequence"};

std::string DefaultClocked(const std::string& place, const std::string& items) {
  if (place == "default module") return PlacedTop(kEdgeStimulus, items);
  std::string unit =
      place == "default checker"
          ? "checker w(clk, a, b, c, d);\n" + items + "endchecker\n"
          : place.substr(8) + " w(input logic clk, a, b, c, d);\n" + items +
                "end" + place.substr(8) + "\n";
  return unit + PlacedTop(kEdgeStimulus, "  w u(clk, a, b, c, d);\n");
}

std::string JoinSource(const std::string& place, const std::string& directive,
                       const std::string& body) {
  if (place == "clocked procedural") {
    return PlacedTop(
        kEdgeStimulus,
        "  always @(posedge clk)" +
            PlacedDirective(directive, "@(posedge clk) " + body).substr(1));
  }
  if (place == "module sequence") {
    return PlacedTop(kEdgeStimulus, "  sequence S; @(posedge clk) " + body +
                                        "; endsequence\n" +
                                        PlacedDirective(directive, "S"));
  }
  if (place.starts_with("default ")) {
    return DefaultClocked(
        place, "  default clocking cb @(posedge clk); endclocking\n" +
                   PlacedDirective(directive, body));
  }
  return PropertyPlaceSource(place, directive, body, kEdgeStimulus);
}

template <typename Places, typename Rows>
void ExpectJoinsIn(const Places& places, const Rows& rows) {
  for (const char* name : places) {
    std::string place = name;
    for (const PlacedProperty& row : rows) {
      for (const char* directive : {"assert", "assume"}) {
        SCOPED_TRACE(place + " " + directive + " " + row.body);
        EXPECT_EQ(CountThroughTheEnd(JoinSource(place, directive, row.body)),
                  row.asserted);
      }
      SCOPED_TRACE(place + " cover " + row.body);
      EXPECT_EQ(CountThroughTheEnd(JoinSource(place, "cover", row.body)),
                (PlaceCounts{row.covered, 0}));
    }
  }
}

constexpr const char* kDefaultClockedPlaces[] = {
    "default module", "default interface", "default program",
    "default checker"};

TEST(MulticlockSequenceRun, AJoinMovesToTheSecondClocksTickInEachPlace) {
  ExpectJoinsIn(kStaticPlaces, kJoinsToAnotherClock);
}

TEST(MulticlockSequenceRun, AJoinUnderTheDefaultClockingMovesToTheSecondClock) {
  ExpectJoinsIn(kDefaultClockedPlaces, kJoinsToAnotherClock);
}

TEST(MulticlockSequenceRun,
     DISABLED_AJoinMovesToTheSecondClocksTickInAClockedProcedure) {
  ExpectJoinsIn(std::initializer_list<const char*>{"clocked procedural"},
                kJoinsToAnotherClock);
}

TEST(MulticlockSequenceRun,
     DISABLED_AJoinMovesToTheSecondClocksTickInAPackageProperty) {
  ExpectJoinsIn(std::initializer_list<const char*>{"package property"},
                kJoinsToAnotherClock);
}

TEST(MulticlockSequenceRun, AJoinOnTheClockInForceChangesNothingInEachPlace) {
  ExpectJoinsIn(kStaticPlaces, kJoinsOnTheClockInForce);
  ExpectJoinsIn(kDefaultClockedPlaces, kJoinsOnTheClockInForce);
  ExpectJoinsIn(
      std::initializer_list<const char*>{"procedural", "clocked procedural",
                                         "package property"},
      kJoinsOnTheClockInForce);
}

TEST(MulticlockSequenceRun, DISABLED_AJoinCountsInACompilationUnitProperty) {
  const std::initializer_list<const char*> kUnit = {"unit"};
  ExpectJoinsIn(kUnit, kJoinsToAnotherClock);
  ExpectJoinsIn(kUnit, kJoinsOnTheClockInForce);
}

}  // namespace
