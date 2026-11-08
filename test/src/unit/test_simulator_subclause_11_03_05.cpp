#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

inline std::string Mod(const std::string& body) {
  return "module t;\n"
         "  logic [7:0] a, b, q, cnt;\n"
         "  function logic incr(inout logic [7:0] c);\n"
         "    c = c + 8'd1;\n"
         "    return 1'b1;\n"
         "  endfunction\n"
         "  initial begin\n"
         "    cnt = 8'd0;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

TEST(ShortCircuit, LogicalAndFalseLhsSkipsRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a && incr(cnt);\n"),
                      "cnt"),
            0u);
}

TEST(ShortCircuit, LogicalOrTrueLhsSkipsRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a || incr(cnt);\n"),
                      "cnt"),
            0u);
}

TEST(ShortCircuit, ImplicationFalseLhsSkipsRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a -> incr(cnt);\n"),
                      "cnt"),
            0u);
}

TEST(ShortCircuit, ConditionalTrueSkipsUnselectedBranchCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a ? incr(cnt) : incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, ConditionalFalseSkipsUnselectedBranchCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a ? incr(cnt) : incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, LogicalAndTrueLhsEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a && incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, LogicalOrFalseLhsEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a || incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, ImplicationTrueLhsEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a -> incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, BitwiseAndZeroLhsStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a & incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, BitwiseOrAllOnesLhsStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'hFF;\n"
                          "    q = a | incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, EquivalenceStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a <-> incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, AdditionStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a + incr(cnt);\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, EqualityStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd5;\n"
                          "    q = (a == incr(cnt));\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, LrmBitwiseFormEvaluatesNestedCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    b = 8'd0;\n"
                          "    q = a & (b | incr(cnt));\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, LrmLogicalFormSkipsNestedCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    b = 8'd0;\n"
                          "    q = a && (b || incr(cnt));\n"),
                      "cnt"),
            0u);
}

TEST(ShortCircuit, LogicalAndShortCircuitsInIfCondition) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    if (a && incr(cnt)) q = 8'd1;\n"),
                      "cnt"),
            0u);
}

TEST(ShortCircuit, LogicalAndEvaluatesInIfCondition) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    if (a && incr(cnt)) q = 8'd1;\n"),
                      "cnt"),
            1u);
}

TEST(ShortCircuit, AndChainShortCircuitsPerAssociativity) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    b = 8'd1;\n"
                          "    q = a && b && incr(cnt);\n"),
                      "cnt"),
            0u);
}

TEST(ShortCircuit, AndChainEvaluatesWhenLeadingOperandsTrue) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    b = 8'd1;\n"
                          "    q = a && b && incr(cnt);\n"),
                      "cnt"),
            1u);
}

}  // namespace
