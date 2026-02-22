// §17.2: Checker declaration

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
  CompilationUnit *Parse(const std::string &src) {
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

static bool HasItemOfKind(const std::vector<ModuleItem *> &items,
                          ModuleItemKind kind) {
  for (const auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

namespace {

// =============================================================================
// §17.1 Basic checker declaration
// =============================================================================
TEST_F(CheckerParseTest, EmptyChecker) {
  auto *unit = Parse("checker my_check; endchecker");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
  EXPECT_TRUE(unit->checkers[0]->items.empty());
}

TEST_F(CheckerParseTest, CheckerWithEndLabel) {
  auto *unit = Parse(R"(
    checker labeled_check;
    endchecker : labeled_check
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "labeled_check");
}

// =============================================================================
// §17.2 Checker ports
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithInputPorts) {
  auto *unit = Parse(R"(
    checker port_check(input logic clk, input logic rst);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_GE(unit->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(unit->checkers[0]->ports[0].name, "clk");
  EXPECT_EQ(unit->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(unit->checkers[0]->ports[1].name, "rst");
  EXPECT_EQ(unit->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST_F(CheckerParseTest, CheckerWithOutputPorts) {
  auto *unit = Parse(R"(
    checker out_check(input logic clk, output logic valid);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_GE(unit->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(unit->checkers[0]->ports[1].name, "valid");
  EXPECT_EQ(unit->checkers[0]->ports[1].direction, Direction::kOutput);
}

TEST_F(CheckerParseTest, CheckerWithNoPorts) {
  auto *unit = Parse(R"(
    checker no_ports;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
}

TEST_F(CheckerParseTest, CheckerWithEmptyParenPorts) {
  auto *unit = Parse(R"(
    checker empty_parens();
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
}

// =============================================================================
// §17.3 Checker body with properties and sequences
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithPropertyDecl) {
  auto *unit = Parse(R"(
    checker prop_check(input logic clk, input logic a, input logic b);
      property p1;
        a |-> b;
      endproperty
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kPropertyDecl));
}

TEST_F(CheckerParseTest, CheckerWithSequenceDecl) {
  auto *unit = Parse(R"(
    checker seq_check(input logic clk, input logic a);
      sequence s1;
        a;
      endsequence
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kSequenceDecl));
}

// =============================================================================
// §17.7 Multiple checkers
// =============================================================================
TEST_F(CheckerParseTest, MultipleCheckers) {
  auto *unit = Parse(R"(
    checker c1; endchecker
    checker c2; endchecker
    checker c3; endchecker
  )");
  EXPECT_EQ(unit->checkers.size(), 3u);
  EXPECT_EQ(unit->checkers[0]->name, "c1");
  EXPECT_EQ(unit->checkers[1]->name, "c2");
  EXPECT_EQ(unit->checkers[2]->name, "c3");
}

// =============================================================================
// §17.8 Checker coexists with module and program
// =============================================================================
TEST_F(CheckerParseTest, CheckerCoexistsWithModuleAndProgram) {
  auto *unit = Parse(R"(
    module m; endmodule
    program p; endprogram
    checker c; endchecker
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->checkers.size(), 1u);
}

// =============================================================================
// §17.9 Checker with assert property
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithAssertProperty) {
  auto *unit = Parse(R"(
    checker assert_check(input logic clk, input logic a, input logic b);
      assert property (@(posedge clk) a |-> b);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kAssertProperty));
}

// =============================================================================
// §17.13 Checker with continuous assignment
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithContAssign) {
  auto *unit = Parse(R"(
    checker assign_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kContAssign));
}

}  // namespace
