#include "fixture_elaborator.h"

using namespace delta;

// =============================================================================
// LRM §3.12.1 — Compilation units (Elaboration)
// =============================================================================

// 14. Elaboration: CU-scope function at top level, module elaborates ok.
TEST(ElabClause03, Cl3_12_1_ElabModuleWithCuFunction) {
  // The CU has a top-level function and a module.
  // Elaboration of the module should succeed.
  EXPECT_TRUE(
      ElabOk("function int cu_func(int x); return x; endfunction\n"
             "module m;\n"
             "  logic [7:0] data;\n"
             "endmodule\n"));
}
