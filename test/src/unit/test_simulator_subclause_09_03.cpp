#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(BlockStatementSimulation, SequentialBlockExecutesInGivenOrder) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a, b;\n"
                      "  initial\n"
                      "    if (1'b1)\n"
                      "      begin\n"
                      "        a = 8'd5;\n"
                      "        b = a + 8'd1;\n"
                      "      end\n"
                      "endmodule\n",
                      "b"),
            6u);
}

TEST(BlockStatementSimulation, ParallelBlockMembersExecuteConcurrently) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  event ev;\n"
                      "  logic [7:0] a;\n"
                      "  initial fork\n"
                      "    begin @(ev); a = 8'd1; end\n"
                      "    begin #5 ->ev; end\n"
                      "  join\n"
                      "endmodule\n",
                      "a"),
            1u);
}

}  // namespace
