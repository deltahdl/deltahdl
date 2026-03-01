// §31.9.1: Requirements for accurate simulation

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string& src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using ConfigParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §31.9 Extended $setuphold arguments
// =============================================================================
TEST_F(SpecifyTest, SetupholdWithDelayedSignals) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, -10, 20, ntfr, , , dCLK, dD);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(tc.notifier, "ntfr");
  EXPECT_EQ(tc.delayed_ref, "dCLK");
  EXPECT_EQ(tc.delayed_data, "dD");
}

}  // namespace
