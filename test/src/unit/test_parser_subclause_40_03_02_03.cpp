#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(DataReadApiParsing, CoverageGetSystemCall) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        int val;
        val = $coverage_get(0, 0);
      end
    endmodule
  )"));
}

}  // namespace
