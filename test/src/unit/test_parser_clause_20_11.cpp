// §20.11: Assertion control system tasks

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
// §39 Assertion control system functions
// =============================================================================
TEST_F(ApiParseTest, AssertOnSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOn;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertOffSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOff;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertKillSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertKill;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// LRM section 39.4.1 -- Placing assertion system callbacks
// These system tasks control assertion processing at the system level:
// $assertOn, $assertOff, $assertKill
// =============================================================================
TEST(ParserSection39, AssertOnNoArgs) {
  // $assertOn with no arguments enables all assertions
  auto r = Parse(R"(
    module m;
      initial $asserton;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
