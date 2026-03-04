#include "fixture_elaborator.h"

using namespace delta;

TEST(ElabClause03, Cl3_12_1_ElabModuleWithCuFunction) {
  EXPECT_TRUE(
      ElabOk("function int cu_func(int x); return x; endfunction\n"
             "module m;\n"
             "  logic [7:0] data;\n"
             "endmodule\n"));
}
