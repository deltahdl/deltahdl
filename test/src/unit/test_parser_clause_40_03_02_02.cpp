// §40.3.2.2: $coverage_get_max

#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(ApiParseTest, CoverageGetMaxSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial begin
        int x;
        x = $coverage_get_max(0, 0);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
