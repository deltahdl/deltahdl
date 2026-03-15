// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, LocalScopesDoNotConflict) {
  EXPECT_TRUE(
      ElabOk("module a; logic x; endmodule\n"
             "module b; logic x; endmodule\n"));
}

}  // namespace
