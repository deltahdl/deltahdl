// §32.9: Loading timing data from an SDF file

#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// §41 Data read API / General system functions
// =============================================================================
TEST_F(ApiParseTest, SdfAnnotateSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf");
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
