// §17.5: Checker procedures

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Parse-level fixture
// =============================================================================
struct CheckerParseTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// Elaboration fixture
// =============================================================================
struct CheckerElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static bool HasItemOfKind(const std::vector<ModuleItem*>& items,
                          ModuleItemKind kind) {
  for (const auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

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

}  // namespace
