// §17.7.2: Checker variable randomization with assumptions

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

TEST_F(VerifyParseTest, CheckerWithAssumeProperty) {
  auto* unit = Parse(R"(
    checker observer_model(bit valid, reset);
      default clocking @$global_clock; endclocking
      rand bit flag;
      m1: assume property (reset |=> !flag);
      m2: assume property (!reset && flag |=> flag);
      m3: assume property ($rising_gclk(flag) |-> valid);
    endchecker : observer_model
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "observer_model");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

}  // namespace
