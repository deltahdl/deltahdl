// §17.4: Context inference

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string& src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using VerifyParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §17.4 Context inference
// =============================================================================
TEST_F(VerifyParseTest, CheckerContextInferenceDefaults) {
  auto* unit = Parse(R"(
    checker check_in_context(logic test_sig,
        event clock = $inferred_clock,
        logic reset = $inferred_disable);
      property p(logic sig);
        sig;
      endproperty
      a1: assert property (@clock disable iff (reset) p(test_sig));
    endchecker : check_in_context
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "check_in_context");
  EXPECT_GE(unit->checkers[0]->ports.size(), 3u);
}

}  // namespace
