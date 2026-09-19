#include <gtest/gtest.h>

#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(ApiParseTest, CoverageControlSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $coverage_control(1, 2, 3);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
