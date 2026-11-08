#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CovergroupInstanceSim, SampleArgumentsBindToSampleFormals) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  covergroup cg with function sample(int x);\n"
                       "    coverpoint x { bins lo = {1}; bins hi = {3}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin c.sample(3); $display(\"cov=%0.2f\", "
                       "c.get_inst_coverage()); end\n"
                       "endmodule\n",
                       f),
            "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
