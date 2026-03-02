// §17.7: Checker variables

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

TEST_F(CheckerParseTest, CheckerWithBitVector) {
  auto* unit = Parse(R"(
    checker bv_check;
      logic [7:0] counter;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

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

TEST_F(VerifyParseTest, CheckerWithRandVariable) {
  auto* unit = Parse(R"(
    checker observer_model(bit valid, reset);
      default clocking @$global_clock; endclocking
      rand bit flag;
    endchecker : observer_model
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "observer_model");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithRandConstVariable) {
  auto* unit = Parse(R"(
    checker reason_about_one_bit(bit [63:0] data1, bit [63:0] data2,
                                  event clock);
      rand const bit [5:0] idx;
      a1: assert property (@clock data1[idx] == data2[idx]);
    endchecker : reason_about_one_bit
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "reason_about_one_bit");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

}  // namespace
