#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(DataReadApiParsing, CoverageMergeSystemCall) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_merge("database.ucdb");
    endmodule
  )"));
}

}  // namespace
