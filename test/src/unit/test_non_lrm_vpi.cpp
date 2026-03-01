// Non-LRM internal VPI infrastructure tests.

#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

TEST(NonLrmVpi, DefaultContextIsAvailable) {
  SetGlobalVpiContext(nullptr);
  VpiContext& ctx = GetGlobalVpiContext();
  (void)ctx;
}

TEST(VpiCompatL2, HeaderIncludable) {
  // Simply including the header should compile.
  SUCCEED();
}

// =============================================================================
// Annex K/L/M - VPI headers (VPI-backed system tasks/functions)
// =============================================================================
TEST_F(AnnexHParseTest, AnnexKVpiSystemCalls) {
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $vpi_get_time;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

}  // namespace
}  // namespace delta
