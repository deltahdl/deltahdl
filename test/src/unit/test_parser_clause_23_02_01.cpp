// §23.2.1: Module header definition

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// 27. Module with static lifetime qualifier
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticModuleLifetime) {
  EXPECT_TRUE(
      ParseOk("module static m;\n"
              "  function int fn();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
}

}  // namespace
