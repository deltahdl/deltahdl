#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, FunctionWithReturnElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, VoidFunctionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void log(int v);\n"
             "    $display(\"%0d\", v);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, TaskElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  task do_work;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, TaskAndFunctionCoexistElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "  task do_nothing; endtask\n"
             "endmodule\n"));
}

}  // namespace
