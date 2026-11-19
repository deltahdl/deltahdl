#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ModulePathSourcesRun, EachSourceDelaysTheSharedDestinationByItsOwnPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(input a, input b, output q);\n"
                       "  assign q = a ^ b;\n"
                       "  specify\n"
                       "    (a => q) = 10;\n"
                       "    (b => q) = 12;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a, b;\n"
                       "  wire tq;\n"
                       "  m u(.a(a), .b(b), .q(tq));\n"
                       "  always @(tq) if ($time >= 50)\n"
                       "    $display(\"t=%0t q=%b\", $time, tq);\n"
                       "  initial begin\n"
                       "    a = 0; b = 0;\n"
                       "    #50 a = 1;\n"
                       "    #50 b = 1;\n"
                       "    #50 a = 0;\n"
                       "    #50 b = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=60 q=1\nt=112 q=0\nt=160 q=1\nt=212 q=0\n");
}

}  // namespace
