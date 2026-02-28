// §32.9: Loading timing data from an SDF file

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
// §41 Data read API / General system functions
// =============================================================================
TEST_F(ApiParseTest, SdfAnnotateSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf");
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
