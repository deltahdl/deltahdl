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

std::string JoinSource(const std::string& place, const std::string& directive,
                       const std::string& body) {
  if (place == "module sequence") {
    return PlacedTop(kEdgeStimulus, "  sequence S; @(posedge clk) " + body +
                                        "; endsequence\n" +
                                        PlacedDirective(directive, "S"));
  }
  return ClockedPlaceSource(place, directive, body, kEdgeStimulus);
}

template <typename Places, typename Rows>
void ExpectJoinsIn(const Places& places, const Rows& rows) {
  ExpectCountsInEachPlace(places, rows, JoinSource);
}

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
