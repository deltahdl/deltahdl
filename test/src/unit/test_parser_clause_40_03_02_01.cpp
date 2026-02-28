// §40.3.2.1: $coverage_control

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =============================================================================
// §40 Coverage control system functions
// =============================================================================
TEST_F(ApiParseTest, CoverageControlSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $coverage_control(1, 2, 3);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
