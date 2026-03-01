// §15.3: Semaphores

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex G - Std package: semaphore class (§G.2)
// =============================================================================
TEST_F(AnnexHParseTest, AnnexGSemaphoreAllMethods) {
  // Semaphore method calls (get, put, try_get) as member-access expressions.
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    sem.put(1);\n"
      "    if (sem.try_get(1)) begin\n"
      "      $display(\"acquired\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
