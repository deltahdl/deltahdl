#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_counter_property_counts.h"

namespace {

constexpr const char* kVacuousPassesOff = "  initial $assertvacuousoff;\n";

void ExpectPassesOfWhichNonvacuous(const std::string& spec, uint64_t passes,
                                   uint64_t nonvacuous) {
  ExpectCounterPropertyCounts(spec, passes, 0);
  ExpectCounterPropertyCounts(spec, nonvacuous, 0, kVacuousPassesOff);
}

TEST(NonVacuityLocalsAtARun, AnAntecedentThatAssignsALocalMustMatch) {
  ExpectPassesOfWhichNonvacuous("(v[0], x = v) |-> ##1 (v == x + 1)", 9, 4);
  ExpectPassesOfWhichNonvacuous("(1, x = v) |-> ##1 (v == x + 1)", 9, 9);
}

TEST(NonVacuityLocalsAtARun, AConsequentIsJudgedUnderTheAntecedentsLocal) {
  ExpectPassesOfWhichNonvacuous(
      "(1, x = v) |-> ((v == x) |-> ##1 (v == x + 1))", 9, 9);
  ExpectPassesOfWhichNonvacuous(
      "(1, x = v) |-> ((v == x + 1) |-> ##1 (v == x + 5))", 10, 0);
}

TEST(NonVacuityLocalsAtARun, EitherOperandOfOrOrAndMakesAPassNonvacuous) {
  for (const char* op : {"or", "and"}) {
    const std::string kOp = std::string(") ") + op + " (";
    ExpectPassesOfWhichNonvacuous(
        "(1, x = v) |-> (((v == x + 1) |-> 0" + kOp + "(v == x) |-> 1))", 10,
        10);
    ExpectPassesOfWhichNonvacuous(
        "(1, x = v) |-> (((v == x) |-> 1" + kOp + "(v == x + 1) |-> 0))", 10,
        10);
    ExpectPassesOfWhichNonvacuous(
        "(1, x = v) |-> (((v == x + 1) |-> 0" + kOp + "(v == x + 2) |-> 0))",
        10, 0);
  }
}

TEST(NonVacuityLocalsAtARun, NexttimeIsJudgedAtTheNextTickUnderTheLocal) {
  ExpectPassesOfWhichNonvacuous("(1, x = v) |-> nexttime ((v == x + 1) |-> 1)",
                                9, 9);
  ExpectPassesOfWhichNonvacuous("(1, x = v) |-> nexttime ((v == x) |-> 0)", 9,
                                0);
}

TEST(NonVacuityLocalsAtARun, UntilNeedsANonvacuousOperandUnderTheLocal) {
  ExpectPassesOfWhichNonvacuous(
      "(1, x = v) |-> (((v == x + 9) |-> 0) until ((v == x) |-> 1))", 10, 10);
  ExpectPassesOfWhichNonvacuous(
      "(1, x = v) |-> (((v == x + 9) |-> 0) until ((v == x + 1) |-> 1))", 10,
      0);
}

}  // namespace
