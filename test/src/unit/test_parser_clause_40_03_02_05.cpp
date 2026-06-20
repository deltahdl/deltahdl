#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(DataReadApiParsing, CoverageSaveSystemCall) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_save("coverage.ucdb");
    endmodule
  )"));
}

}  // namespace
