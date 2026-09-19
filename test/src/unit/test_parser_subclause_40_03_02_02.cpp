#include <gtest/gtest.h>

#include "fixture_program.h"

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
