// §13.4.4: Background processes spawned by function calls

#include "fixture_elaborator.h"

using namespace delta;

// Elab test fixture
namespace {

// =============================================================================
// A.6.3 Parallel and sequential blocks — Elaboration
// =============================================================================
// ---------------------------------------------------------------------------
// Elaboration: §13.4 fork restrictions inside functions
// ---------------------------------------------------------------------------
// §13.4.4: fork/join_none is permitted inside a function
TEST(ElabA603, ForkJoinNoneAllowedInFunction) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.4: fork/join_any is illegal inside a function
TEST(ElabA603, ForkJoinAnyIllegalInFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_any\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
