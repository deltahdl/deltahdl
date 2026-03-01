// §40.3.2.5: $coverage_save

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

namespace {

TEST(ParserSection40, CoverageSaveSystemCall) {
  // $coverage_save saves coverage data to file
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_save("coverage.ucdb");
    endmodule
  )"));
}

}  // namespace
