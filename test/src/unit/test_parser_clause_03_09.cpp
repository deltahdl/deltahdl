// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, LocalScopesDoNotConflict) {
  EXPECT_TRUE(
      ParseOk("module a; logic x; endmodule\n"
              "module b; logic x; endmodule\n"));
}

}  // namespace
