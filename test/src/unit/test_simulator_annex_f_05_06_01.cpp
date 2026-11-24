#include <gtest/gtest.h>

#include <string>

#include "helpers_counter_property_counts.h"

namespace {

TEST(NeutralSatisfactionLocalsAtARun, EachOperandOfOrReadsTheIncomingLocal) {
  ExpectCounterPropertyCounts("(1, x = v) |-> ((v == x) or (v == x + 1))", 10,
                              0);
  ExpectCounterPropertyCounts("(1, x = v) |-> ((v == x + 1) or (v == x))", 10,
                              0);
  ExpectCounterPropertyCounts("(1, x = v) |-> ((v == x + 1) or (v == x + 2))",
                              0, 10);
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> ((##1 (v == x + 2)) or (##1 (v == x + 1)))", 9, 0);
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> ((##1 (v == x)) or (##1 (v == x + 2)))", 0, 9);
}

TEST(NeutralSatisfactionLocalsAtARun, EachOperandOfAndReadsTheIncomingLocal) {
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> ((v == x) and (##1 (v == x + 1)))", 9, 0);
  ExpectCounterPropertyCounts("(1, x = v) |-> ((v == x) and (##1 (v == x)))", 0,
                              9);
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> ((v == x + 1) and (##1 (v == x + 1)))", 0, 10);
}

TEST(NeutralSatisfactionLocalsAtARun, TheOperandOfNotReadsTheIncomingLocal) {
  ExpectCounterPropertyCounts("(1, x = v) |-> not (v == x + 1)", 10, 0);
  ExpectCounterPropertyCounts("(1, x = v) |-> not (v == x)", 0, 10);
  ExpectCounterPropertyCounts("(1, x = v) |-> not (##1 (v == x))", 9, 0);
  ExpectCounterPropertyCounts("(1, x = v) |-> not (##1 (v == x + 1))", 0, 9);
}

TEST(NeutralSatisfactionLocalsAtARun,
     StrongAndWeakSequencesReadTheIncomingLocal) {
  for (const char* strength : {"strong", "weak"}) {
    const std::string kLead = std::string("(1, x = v) |-> ") + strength;
    ExpectCounterPropertyCounts(kLead + "(##1 (v == x + 1))", 9, 0);
    ExpectCounterPropertyCounts(kLead + "(##1 (v == x))", 0, 9);
  }
}

TEST(NeutralSatisfactionLocalsAtARun, TheOperandOfNexttimeKeepsTheLocal) {
  ExpectCounterPropertyCounts("(1, x = v) |-> nexttime (v == x + 1)", 9, 0);
  ExpectCounterPropertyCounts("(1, x = v) |-> nexttime (v == x)", 0, 9);
}

TEST(NeutralSatisfactionLocalsAtARun, BothOperandsOfUntilKeepTheLocal) {
  ExpectCounterPropertyCounts("(1, x = v) |-> ((v < x + 3) until (v == x + 3))",
                              7, 0);
  ExpectCounterPropertyCounts("(1, x = v) |-> ((v < x + 2) until (v == x + 3))",
                              0, 8);
}

TEST(NeutralSatisfactionLocalsAtARun, TheOperandOfAcceptOnReadsTheLocal) {
  const std::string kStop =
      "  logic stop = 0;\n"
      "  initial begin #48 stop = 1; #4 stop = 0; end\n";
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> accept_on (stop) ((v == x) ##1 (v == x + 1))", 9, 0,
      kStop);
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> accept_on (stop) ((v == x) ##1 (v == x + 2))", 1, 8,
      kStop);
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> accept_on (stop) ((v == x + 1) ##1 (v == x + 2))", 0, 10,
      kStop);
}

TEST(NeutralSatisfactionLocalsAtARun,
     ANestedDeclarationOfTheSameNameIsAVariableOfItsOwn) {
  const std::string kInner =
      "  property inner(int base);\n"
      "    int x;\n"
      "    (1, x = base + 1) |-> ##1 (v == x);\n"
      "  endproperty\n";
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> (inner(x) and (##1 (v == x + 1)))", 9, 0, kInner);
  ExpectCounterPropertyCounts("(1, x = v) |-> (inner(x) and (##1 (v == x)))", 0,
                              9, kInner);
  ExpectCounterPropertyCounts(
      "(1, x = v) |-> (inner(x + 1) and (##1 (v == x + 1)))", 0, 9, kInner);
}

TEST(NeutralSatisfactionLocalsAtARun,
     ADisabledAttemptHoldingALocalNeitherPassesNorFails) {
  const std::string kPulse = "  initial begin #42 rst = 1; #6 rst = 0; end\n";
  ExpectCounterPropertyCounts(
      "disable iff (rst) (1, x = v) |-> ##2 (v == x + 2)", 5, 0, kPulse);
  ExpectCounterPropertyCounts(
      "disable iff (rst) (1, x = v) |-> ##2 (v == x + 3)", 0, 5, kPulse);
  ExpectCounterPropertyCounts(
      "disable iff (rst) (1, x = v) |-> ##2 (v == x + 2)", 8, 0);
}

}  // namespace
