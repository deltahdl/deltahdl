#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

struct ConnectionCase {
  std::string ports;
  std::string body;
  std::string path;
  std::string top_decl;
  std::string connect;
  std::string stimulus;
};

std::string ConnectionRun(const ConnectionCase& c) {
  SimFixture f;
  return RunCapture("module leaf" + c.ports + ";\n  " + c.body +
                        "\n  specify\n    " + c.path +
                        "\n  endspecify\nendmodule\n"
                        "module top;\n  " +
                        c.top_decl + "\n  leaf u(" + c.connect +
                        ");\n"
                        "  always @(y) if ($time >= 10)\n"
                        "    $display(\"t=%0t y=%b\", $time, y);\n"
                        "  initial begin\n    " +
                        c.stimulus + "\n  end\nendmodule\n",
                    f);
}

TEST(FullAndParallelConnectionRun, FullPathDelaysAnotherBitPosition) {
  EXPECT_EQ(ConnectionRun({"(input [1:0] a, output [1:0] y)",
                           "assign y = {a[0], 1'b0};", "(a *> y) = 7;",
                           "logic [1:0] a; wire [1:0] y;", ".a(a), .y(y)",
                           "a = 0; #20 a = 2'b01;"}),
            "t=27 y=10\n");
}

TEST(FullAndParallelConnectionRun, FullPathDelaysAScalarFromAnyVectorBit) {
  EXPECT_EQ(
      ConnectionRun({"(input [3:0] a, output y)", "assign y = |a;",
                     "(a *> y) = 6;", "logic [3:0] a; wire y;", ".a(a), .y(y)",
                     "a = 0; #20 a = 4'b0100; #20 a = 0;"}),
      "t=26 y=1\nt=46 y=0\n");
}

TEST(FullAndParallelConnectionRun, FullPathDelaysEveryBitFromAScalar) {
  EXPECT_EQ(ConnectionRun({"(input s, output [3:0] y)", "assign y = {4{s}};",
                           "(s *> y) = 5;", "logic s; wire [3:0] y;",
                           ".s(s), .y(y)", "s = 0; #20 s = 1;"}),
            "t=25 y=1111\n");
}

TEST(FullAndParallelConnectionRun, FullPathBetweenVectorsOfDifferentWidths) {
  EXPECT_EQ(ConnectionRun({"(input [3:0] a, output [1:0] y)",
                           "assign y = {a[0], a[3]};", "(a *> y) = 4;",
                           "logic [3:0] a; wire [1:0] y;", ".a(a), .y(y)",
                           "a = 0; #20 a = 4'b1001;"}),
            "t=24 y=11\n");
}

TEST(FullAndParallelConnectionRun, DISABLED_ParallelPathDelaysEachBitOnItsOwn) {
  EXPECT_EQ(ConnectionRun({"(input [3:0] a, output [3:0] y)", "assign y = a;",
                           "(a => y) = (3, 4);", "logic [3:0] a; wire [3:0] y;",
                           ".a(a), .y(y)",
                           "a = 0; #20 a = 4'b0101; #20 a = 4'b1010;"}),
            "t=23 y=0101\nt=43 y=1111\nt=44 y=1010\n");
}

TEST(FullAndParallelConnectionRun, ParallelPathLeavesOtherBitsUnchanged) {
  EXPECT_EQ(ConnectionRun({"(input [3:0] a, output [3:0] y)", "assign y = a;",
                           "(a => y) = 5;", "logic [3:0] a; wire [3:0] y;",
                           ".a(a), .y(y)",
                           "a = 4'b1100; #20 a = 4'b1101; #20 a = 4'b1100;"}),
            "t=25 y=1101\nt=45 y=1100\n");
}

TEST(FullAndParallelConnectionRun, MultiplexerExampleTakesEachPathsDelay) {
  EXPECT_EQ(
      ConnectionRun({"(input [7:0] in1, in2, input s, output [7:0] q)",
                     "assign q = s ? in2 : in1;",
                     "(in1 => q) = (3, 4);\n    (in2 => q) = (2, 3);\n"
                     "    (s *> q) = 1;",
                     "logic [7:0] in1, in2; logic s; wire [7:0] y;",
                     ".in1(in1), .in2(in2), .s(s), .q(y)",
                     "in1 = 0; in2 = 8'hff; s = 0;\n    #20 in1 = 8'h01;\n"
                     "    #20 s = 1;\n    #20 in2 = 8'h00;"}),
      "t=23 y=00000001\nt=41 y=11111111\nt=63 y=00000000\n");
}

TEST(FullAndParallelConnectionRun, DISABLED_ParallelPathFallOfOneBitTakesFall) {
  EXPECT_EQ(ConnectionRun({"(input [3:0] a, output [3:0] y)", "assign y = a;",
                           "(a => y) = (3, 4);", "logic [3:0] a; wire [3:0] y;",
                           ".a(a), .y(y)", "a = 4'b1111; #20 a = 4'b1110;"}),
            "t=24 y=1110\n");
}

TEST(FullAndParallelConnectionRun, DISABLED_FullPathDelaysEachBitOnItsOwn) {
  EXPECT_EQ(ConnectionRun({"(input [1:0] a, output [1:0] y)",
                           "assign y = {a[0], ~a[0]};", "(a *> y) = (3, 4);",
                           "logic [1:0] a; wire [1:0] y;", ".a(a), .y(y)",
                           "a = 0; #20 a = 2'b01;"}),
            "t=23 y=11\nt=24 y=10\n");
}

}  // namespace
