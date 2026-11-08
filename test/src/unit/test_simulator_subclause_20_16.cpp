#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PlaRecognition, TableNameIsDispatchedAndDrivesOutput) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    out = 1'b0;\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

TEST(PlaRecognition, ExtraComponentNameIsNotDispatched) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    out = 1'b0;\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array$extra(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 0u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$sync$and$array$extra is not a system task or "
                            "system function this tool implements",
                            9, "20.1"));
}

}  // namespace
