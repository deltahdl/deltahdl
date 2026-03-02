// §16.14.7: Inferred clocking and disable functions

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

TEST_F(VerifyParseTest, CheckerContextInferenceImplicit) {
  auto* unit = Parse(R"(
    checker check_ctx(logic sig,
        event clock = $inferred_clock);
    endchecker
    module m;
      logic clk, a;
      always @(posedge clk) begin
        check_ctx chk(a);
      end
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
