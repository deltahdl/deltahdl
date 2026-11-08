#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

TEST(ArithmeticSynthesis, AdditionLowersToTheSumOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a + b"),
                    16, [](uint64_t a, uint64_t b) { return (a + b) & 0xFU; });
}

TEST(ArithmeticSynthesis, SubtractionLowersToTheDifferenceOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a - b"),
                    16, [](uint64_t a, uint64_t b) { return (a - b) & 0xFU; });
}

TEST(ArithmeticSynthesis, AdditionByOneAgreesWithTheIncrementOfTheSameOperand) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a + 4'd1"), 1,
                    [](uint64_t a, uint64_t) { return (a + 1) & 0xFU; });
}

TEST(ArithmeticSynthesis, MultiplicationIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a * b",
                       "a multiplied by b", "11.4.3");
}

TEST(ArithmeticSynthesis, DivisionIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a / b",
                       "a divided by b", "11.4.3");
}

TEST(ArithmeticSynthesis, ModulusIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a % b", "a modulo b",
                       "11.4.3");
}

TEST(ArithmeticSynthesis, PowerIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a ** b",
                       "a to the power of b", "11.4.3");
}

TEST(ArithmeticSynthesis, UnaryMinusLowersToTheTwosComplementOfItsOperand) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "-a"), 1,
                    [](uint64_t a, uint64_t) { return (16u - a) & 0xFu; });
}

TEST(ArithmeticSynthesis, UnaryPlusLowersToItsOperandUnchanged) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "+a"), 1,
                    [](uint64_t a, uint64_t) { return a; });
}

}  // namespace
