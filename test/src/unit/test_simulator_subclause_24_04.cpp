#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunToEnd(const std::string& src) {
  SimFixture f;
  auto out = RunCaptureThroughFinals(ElaborateSrc, src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

constexpr const char* kCountingDesign =
    "module top;\n"
    "  logic clk = 0;\n"
    "  logic [7:0] d = 1;\n"
    "  initial repeat (6) #5 clk = ~clk;\n"
    "  always @(posedge clk) d = d + 1;\n";

TEST(ProgramRaceFreeRead,
     DISABLED_AClockingInputReadsTheValueBeforeTheDesignEdge) {
  EXPECT_EQ(RunToEnd(std::string(kCountingDesign) +
                     "  program p;\n"
                     "    clocking cb @(posedge clk);\n"
                     "      input d;\n"
                     "    endclocking\n"
                     "    initial begin\n"
                     "      @(cb);\n"
                     "      $display(\"%0d\", cb.d);\n"
                     "      @(cb);\n"
                     "      $display(\"%0d\", cb.d);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "1\n2\n");
}

TEST(ProgramRaceFreeRead, ADirectReadAtTheEdgeSeesTheDesignsSettledValue) {
  EXPECT_EQ(
      RunToEnd(std::string(kCountingDesign) + "  program p;\n"
                                              "    initial begin\n"
                                              "      @(posedge clk);\n"
                                              "      $display(\"%0d\", d);\n"
                                              "      @(posedge clk);\n"
                                              "      $display(\"%0d\", d);\n"
                                              "    end\n"
                                              "  endprogram\n"
                                              "endmodule\n"),
      "2\n3\n");
}

TEST(ProgramRaceFreeRead, AClockDrivenByANonblockingAssignmentSettlesFirst) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic clk = 0;\n"
                     "  logic [7:0] q = 0;\n"
                     "  logic [7:0] d = 7;\n"
                     "  initial #5 clk <= 1;\n"
                     "  always @(posedge clk) q <= d;\n"
                     "  program p;\n"
                     "    initial begin\n"
                     "      @(posedge clk);\n"
                     "      $display(\"%0d\", q);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "7\n");
}

TEST(ProgramRaceFreeRead, TwoSimultaneousClocksBothSettleBeforeTheProgram) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic clka = 0;\n"
                     "  logic clkb = 0;\n"
                     "  logic [7:0] qa = 0;\n"
                     "  logic [7:0] qb = 0;\n"
                     "  initial begin\n"
                     "    #5 clka = 1;\n"
                     "    clkb <= 1;\n"
                     "  end\n"
                     "  always @(posedge clka) qa <= 7;\n"
                     "  always @(posedge clkb) qb <= 9;\n"
                     "  program p;\n"
                     "    initial begin\n"
                     "      @(posedge clka);\n"
                     "      $display(\"%0d %0d\", qa, qb);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "7 9\n");
}

TEST(ProgramRaceFreeRead,
     DISABLED_AClockingInputOnANonblockingClockReadsTheOldValue) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic clk = 0;\n"
                     "  logic [7:0] q = 3;\n"
                     "  initial #5 clk <= 1;\n"
                     "  always @(posedge clk) q <= 8;\n"
                     "  program p;\n"
                     "    clocking cb @(posedge clk);\n"
                     "      input q;\n"
                     "    endclocking\n"
                     "    initial begin\n"
                     "      @(cb);\n"
                     "      $display(\"%0d %0d\", cb.q, q);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "3 8\n");
}

}  // namespace
