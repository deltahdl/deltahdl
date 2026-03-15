// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, TaskAndFunctionCoexistElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "  task do_nothing; endtask\n"
             "endmodule\n"));
}

}  // namespace
