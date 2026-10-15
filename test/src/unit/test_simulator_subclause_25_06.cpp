#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.6: a signal of an interface reached through a modport is a terminal the
// module's specify block may use, so a module path ending at ch.q delays it as
// the path ending at the output port qo delays qo. The flop's edge at 10
// reaches qo after its rise delay of 2 and ch.q after its rise delay of 5, so
// at 13 qo is 1 and q still x, and at 16 q is 1. Before, the path to ch.q was
// ignored and q was 1 at 13.
TEST(InterfaceSpecifySim, PathDelayToModportSignalIsApplied) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface itf;\n"
                       "  logic c, d, q;\n"
                       "  modport flop(input c, d, output q);\n"
                       "endinterface\n"
                       "module dtype(itf.flop ch, output logic qo);\n"
                       "  always_ff @(posedge ch.c) begin\n"
                       "    ch.q <= ch.d;\n"
                       "    qo <= ch.d;\n"
                       "  end\n"
                       "  specify\n"
                       "    (posedge ch.c => (ch.q +: ch.d)) = (5, 6);\n"
                       "    (posedge ch.c => (qo +: ch.d)) = (2, 3);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  itf i();\n"
                       "  wire qo;\n"
                       "  dtype u(i, qo);\n"
                       "  initial begin i.c = 0; i.d = 1; #10 i.c = 1; end\n"
                       "  initial begin\n"
                       "    #13 $display(\"q=%b qo=%b\", i.q, qo);\n"
                       "    #3 $display(\"q=%b\", i.q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "q=x qo=1\nq=1\n");
}

}  // namespace
