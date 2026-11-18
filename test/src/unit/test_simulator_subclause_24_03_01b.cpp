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

TEST(ProgramReactiveAssign, AProgramAssignNeverShowsTheDesignsActiveValue) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic [7:0] a = 0;\n"
                     "  logic [7:0] b;\n"
                     "  initial begin\n"
                     "    #1 a = 1;\n"
                     "    a <= 2;\n"
                     "  end\n"
                     "  always @(b) if ($time == 1) $display(\"%0d\", b);\n"
                     "  program p;\n"
                     "    assign b = a;\n"
                     "    initial #3;\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "2\n");
}

TEST(ProgramReactiveInitial, AnUninstantiatedTopLevelProgramRunsAfterTheNba) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrcAllTops,
                                    "module t;\n"
                                    "  int x;\n"
                                    "  initial begin\n"
                                    "    x = 0;\n"
                                    "    x <= 5;\n"
                                    "  end\n"
                                    "endmodule\n"
                                    "program p;\n"
                                    "  initial $display(\"%0d\", t.x);\n"
                                    "endprogram\n",
                                    f),
            "5\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProgramReactiveInitial, AProgramNestedInAnInterfaceRunsAfterItsNba) {
  EXPECT_EQ(RunToEnd("interface Bus;\n"
                     "  int a;\n"
                     "  initial begin\n"
                     "    a = 0;\n"
                     "    a <= 3;\n"
                     "  end\n"
                     "  program p;\n"
                     "    initial $display(\"%0d\", a);\n"
                     "  endprogram\n"
                     "endinterface\n"
                     "module top;\n"
                     "  Bus s();\n"
                     "endmodule\n"),
            "3\n");
}

TEST(ProgramReactiveSubroutine, TheProgramsOwnTaskRunsInTheReactiveRegion) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic [7:0] v;\n"
                     "  initial v <= 10;\n"
                     "  program p;\n"
                     "    task t;\n"
                     "      v = 99;\n"
                     "    endtask\n"
                     "    initial begin\n"
                     "      t();\n"
                     "      #1 $display(\"%0d\", v);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "99\n");
}

TEST(ProgramReactiveSubroutine, AnInterfaceTaskCalledFromAProgramRunsReactive) {
  EXPECT_EQ(RunToEnd("interface I;\n"
                     "  logic [7:0] v;\n"
                     "  task set_v;\n"
                     "    v = 99;\n"
                     "  endtask\n"
                     "  initial v <= 10;\n"
                     "endinterface\n"
                     "module top;\n"
                     "  I i();\n"
                     "  program p;\n"
                     "    initial begin\n"
                     "      i.set_v();\n"
                     "      #1 $display(\"%0d\", i.v);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "99\n");
}

TEST(ProgramReactiveSubroutine,
     AStatementAfterADelayInADesignTaskRunsReactive) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic [7:0] a;\n"
                     "  logic [7:0] b = 0;\n"
                     "  task T;\n"
                     "    #5;\n"
                     "    a = b;\n"
                     "  endtask\n"
                     "  initial #5 b <= 1;\n"
                     "  program p;\n"
                     "    initial begin\n"
                     "      T();\n"
                     "      $display(\"%0d\", a);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "1\n");
}

TEST(ProgramReNba, AProgramUpdateIsNotSeenAfterAZeroDelay) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic [7:0] v = 0;\n"
                     "  program p;\n"
                     "    initial begin\n"
                     "      #1 v <= 5;\n"
                     "      #0 $display(\"%0d\", v);\n"
                     "      #1 $display(\"%0d\", v);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "0\n5\n");
}

TEST(ProgramReNba,
     ADesignTaskUpdateCalledFromAProgramIsNotSeenAfterAZeroDelay) {
  EXPECT_EQ(RunToEnd("module top;\n"
                     "  logic [7:0] v = 0;\n"
                     "  task t;\n"
                     "    v <= 5;\n"
                     "  endtask\n"
                     "  program p;\n"
                     "    initial begin\n"
                     "      #1 t();\n"
                     "      #0 $display(\"%0d\", v);\n"
                     "      #1 $display(\"%0d\", v);\n"
                     "    end\n"
                     "  endprogram\n"
                     "endmodule\n"),
            "0\n5\n");
}

constexpr const char* kSampledChecks =
    "  assert property (@(posedge clk) same == 0) $display(\"same ok\");\n"
    "    else $display(\"same bad\");\n"
    "  assert property (@(posedge clk) early == 1) $display(\"early ok\");\n"
    "    else $display(\"early bad\");\n";

constexpr const char* kEdgeWrites =
    "  initial begin\n"
    "    #4 early = 1;\n"
    "    #1 same = 1;\n"
    "    clk = 1;\n"
    "    #1;\n"
    "  end\n";

constexpr const char* kSignals =
    "  logic clk = 0;\n"
    "  logic same = 0;\n"
    "  logic early = 0;\n";

void ExpectPreponedValues(const std::string& src) {
  auto out = RunToEnd(src);
  EXPECT_NE(out.find("same ok"), std::string::npos) << out;
  EXPECT_NE(out.find("early ok"), std::string::npos) << out;
  EXPECT_EQ(out.find("bad"), std::string::npos) << out;
}

TEST(ProgramAssertionSampling, AProgramsOwnVariableWrittenWithItsClock) {
  ExpectPreponedValues(std::string("module top;\n"
                                   "program p;\n") +
                       kSignals + kEdgeWrites + kSampledChecks +
                       "endprogram\n"
                       "endmodule\n");
}

TEST(ProgramAssertionSampling, AnInstantiatedProgramsPortWrittenByTheModule) {
  ExpectPreponedValues(
      std::string("program prg(input logic clk, same, early);\n"
                  "  initial #10;\n") +
      kSampledChecks +
      "endprogram\n"
      "module top;\n" +
      kSignals + "  prg u(.clk(clk), .same(same), .early(early));\n" +
      kEdgeWrites + "endmodule\n");
}

TEST(ProgramAssertionSampling, TheEnclosingModulesVariableInANestedProgram) {
  ExpectPreponedValues(std::string("module top;\n") + kSignals + kEdgeWrites +
                       "program p;\n"
                       "  initial #10;\n" +
                       kSampledChecks +
                       "endprogram\n"
                       "endmodule\n");
}

TEST(ProgramAssertionSampling, AnAssertionInAGenerateBlockOfAProgram) {
  ExpectPreponedValues(std::string("module top;\n"
                                   "program p;\n") +
                       kSignals + kEdgeWrites + "if (1) begin : g\n" +
                       kSampledChecks +
                       "end\n"
                       "endprogram\n"
                       "endmodule\n");
}

}  // namespace
