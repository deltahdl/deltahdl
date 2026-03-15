// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(ModuleDefinitions, ModuleAsContainer) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  wire b;\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

}  // namespace
