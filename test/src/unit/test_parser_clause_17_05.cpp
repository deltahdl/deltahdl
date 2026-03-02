// §17.5: Checker procedures

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §17.5 Checker procedures (always, initial)
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithAlwaysBlock) {
  auto* unit = Parse(R"(
    checker always_check(input logic clk, input logic a);
      always @(posedge clk)
        assert(a);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kAlwaysBlock));
}

TEST_F(CheckerParseTest, CheckerWithInitialBlock) {
  auto* unit = Parse(R"(
    checker init_check;
      initial begin
        $display("checker started");
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kInitialBlock));
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

// =============================================================================
// §17.5 Checker procedures
// =============================================================================
TEST_F(VerifyParseTest, CheckerWithInitialProcedure) {
  auto* unit = Parse(R"(
    checker init_check(input logic clk, input logic rst);
      logic flag;
      initial begin
        flag = 0;
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "init_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithAlwaysComb) {
  auto* unit = Parse(R"(
    checker comb_check(logic a, b);
      logic v;
      always_comb begin
        if (a)
          v = b;
        else
          v = !b;
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "comb_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithFinalProcedure) {
  auto* unit = Parse(R"(
    checker final_check;
      logic count;
      final begin
        $display("count = %0d", count);
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "final_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

}  // namespace
