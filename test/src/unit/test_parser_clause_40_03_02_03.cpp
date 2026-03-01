// §40.3.2.3: $coverage_get

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

namespace {

TEST(ParserSection40, CoverageGetSystemCall) {
  // $coverage_get returns current coverage count
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
