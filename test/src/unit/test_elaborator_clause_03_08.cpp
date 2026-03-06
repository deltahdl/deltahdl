#include "fixture_elaborator.h"

namespace {

// §3.8: Subroutines — tasks and functions.

TEST(ElabClause03, Cl3_8_FunctionWithReturnElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_8_VoidFunctionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void log(int v);\n"
             "    $display(\"%0d\", v);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_8_TaskElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  task do_work;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_8_TaskAndFunctionCoexistElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "  task do_nothing; endtask\n"
             "endmodule\n"));
}

}  // namespace
