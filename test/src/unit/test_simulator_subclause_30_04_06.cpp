#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

TEST(MultiplePathStatementRun, EveryDestinationTakesTheDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mypair(input a, input b, output y1, output "
                       "y2);\n"
                       "  assign y1 = a;\n"
                       "  assign y2 = b;\n"
                       "  specify\n"
                       "    (a, b *> y1, y2) = 4;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a, b;\n"
                       "  wire t1, t2;\n"
                       "  mypair u(.a(a), .b(b), .y1(t1), .y2(t2));\n"
                       "  always @(t1 or t2) if ($time >= 8)\n"
                       "    $display(\"t=%0t y1=%b y2=%b\", $time, t1, t2);\n"
                       "  initial begin\n"
                       "    a = 0; b = 0;\n"
                       "    #10 a = 1;\n"
                       "    #10 b = 1;\n"
                       "    #10 a = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=14 y1=1 y2=0\nt=24 y1=1 y2=1\nt=34 y1=0 y2=1\n");
}

bool HasPath(const SpecifyManager& mgr, std::string_view src,
             std::string_view dst, uint64_t delay, uint64_t reject) {
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst && pd.delays[0] == delay &&
        pd.reject_limit[0] == reject) {
      return true;
    }
  }
  return false;
}

TEST(MultiplePathStatementRun, FirstTerminalsPulseLimitsReachEveryPath) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input a, input b, output y1, output y2);\n"
      "  specify\n"
      "    (a, b *> y1, y2) = 4;\n"
      "    specparam PATHPULSE$a$y1 = (1, 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->GetPathDelays().size(), 4u);
  EXPECT_TRUE(HasPath(*mgr, "a", "y1", 4, 1));
  EXPECT_TRUE(HasPath(*mgr, "b", "y1", 4, 1));
  EXPECT_TRUE(HasPath(*mgr, "a", "y2", 4, 1));
  EXPECT_TRUE(HasPath(*mgr, "b", "y2", 4, 1));
}

std::string ThreeByTwoRun(const std::string& paths) {
  SimFixture f;
  return RunCapture(
      "module leaf(input a, b, c, output q1, q2);\n"
      "  assign q1 = c;\n"
      "  assign q2 = b;\n"
      "  specify\n"
      "    " +
          paths +
          "\n"
          "  endspecify\n"
          "endmodule\n"
          "module top;\n"
          "  logic a, b, c;\n"
          "  wire q1, q2;\n"
          "  leaf u(.a(a), .b(b), .c(c), .q1(q1), .q2(q2));\n"
          "  always @(q1 or q2) if ($time >= 15)\n"
          "    $display(\"t=%0t q1=%b q2=%b\", $time, q1, q2);\n"
          "  initial begin\n"
          "    a = 0; b = 0; c = 0;\n"
          "    #20 c = 1;\n"
          "    #20 b = 1;\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(MultiplePathStatementRun, ListStatementDelaysEveryCrossPair) {
  EXPECT_EQ(ThreeByTwoRun("(a, b, c *> q1, q2) = 10;"),
            "t=30 q1=1 q2=0\nt=50 q1=1 q2=1\n");
}

TEST(MultiplePathStatementRun, ListStatementMatchesSixSinglePaths) {
  EXPECT_EQ(ThreeByTwoRun("(a, b, c *> q1, q2) = 10;"),
            ThreeByTwoRun("(a *> q1) = 10;\n    (b *> q1) = 10;\n"
                          "    (c *> q1) = 10;\n    (a *> q2) = 10;\n"
                          "    (b *> q2) = 10;\n    (c *> q2) = 10;"));
}

TEST(MultiplePathStatementRun, ThreeByTwoListRegistersSixPaths) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input a, b, c, output q1, q2);\n"
      "  specify\n"
      "    (a, b, c *> q1, q2) = 10;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->GetPathDelays().size(), 6u);
  for (const char* src : {"a", "b", "c"}) {
    for (const char* dst : {"q1", "q2"}) {
      EXPECT_TRUE(HasPath(*mgr, src, dst, 10, 10)) << src << " " << dst;
    }
  }
}

TEST(MultiplePathStatementRun, MixedScalarAndVectorListsDelayEveryPair) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf(input s, input [3:0] v, output y,\n"
                       "            output [3:0] w);\n"
                       "  assign y = v[2];\n"
                       "  assign w = {4{s}};\n"
                       "  specify\n"
                       "    (s, v *> y, w) = 6;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic s;\n"
                       "  logic [3:0] v;\n"
                       "  wire y;\n"
                       "  wire [3:0] w;\n"
                       "  leaf u(.s(s), .v(v), .y(y), .w(w));\n"
                       "  always @(y or w) if ($time >= 15)\n"
                       "    $display(\"t=%0t y=%b w=%b\", $time, y, w);\n"
                       "  initial begin\n"
                       "    s = 0; v = 0;\n"
                       "    #20 v = 4'b0100;\n"
                       "    #20 s = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=26 y=1 w=0000\nt=46 y=1 w=1111\n");
}

}  // namespace
