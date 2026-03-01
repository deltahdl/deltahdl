// §40.3.2.4: $coverage_merge

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

namespace {

TEST(ParserSection40, CoverageMergeSystemCall) {
  // $coverage_merge merges coverage databases
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_merge("database.ucdb");
    endmodule
  )"));
}

}  // namespace
