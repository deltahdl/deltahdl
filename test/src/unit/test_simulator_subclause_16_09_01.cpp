#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string PrecedenceSource(const std::string& body,
                             const std::string& drive = "") {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  logic c = 0;\n"
         "  logic d = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  sequence rule;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n" +
         (drive.empty() ? std::string("    #10 a = 1;\n"
                                      "    #10 a = 0; b = 1;\n"
                                      "    #10 b = 0;\n"
                                      "    #10 c = 1;\n"
                                      "    #10 c = 0; d = 1;\n"
                                      "    #10 d = 0;\n")
                        : drive) +
         "    #20 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

TEST(SequenceOperatorPrecedence, ConcatenationBindsTighterThanOr) {
  SimFixture f;
  auto* hits = RunAndFindVar(PrecedenceSource("a ##1 b or c ##1 d"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* either = RunAndFindVar(PrecedenceSource("a or c"), g, "hits");
  ASSERT_NE(either, nullptr);
  EXPECT_EQ(either->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

TEST(SequenceOperatorPrecedence, ConcatenationBindsTighterThanAnd) {
  SimFixture f;
  auto* hits = RunAndFindVar(PrecedenceSource("a ##1 b and c",
                                              "    #10 a = 1; c = 1;\n"
                                              "    #10 a = 0; c = 0; b = 1;\n"
                                              "    #10 b = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

TEST(SequenceOperatorPrecedence, AndBindsTighterThanOr) {
  SimFixture f;
  auto* hits = RunAndFindVar(PrecedenceSource("a and c or d",
                                              "    #10 a = 1; c = 1;\n"
                                              "    #10 a = 0; c = 0; d = 1;\n"
                                              "    #10 d = 0;\n"
                                              "    #10 d = 1;\n"
                                              "    #10 d = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

}  // namespace
