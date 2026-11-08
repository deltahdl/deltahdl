#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"

using namespace delta;

namespace {

TEST(RandseqFormalWidthSim, TypedefNameFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef bit [3:0] nib;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      main : gen(8'hFF) ;\n"
                         "      gen( nib p ) : { r = p; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 15u);
}

TEST(RandseqFormalWidthSim, TypedefNameFormalSizesItsOwnDefaultValue) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef bit [3:0] nib;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      main : gen ;\n"
                         "      gen( nib p = 8'hFF ) : { r = p; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 15u);
}

TEST(RandseqFormalWidthSim, TypedefNameFormalWiderThanOneWordKeepsItsHighBits) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef bit [39:0] wide;\n"
                         "  logic [63:0] r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      main : gen(48'hFFFF00000001) ;\n"
                         "      gen( wide p ) : { r = p; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1095216660481ull);
}

}  // namespace
