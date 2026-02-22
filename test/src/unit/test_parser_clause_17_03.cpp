// §17.3: Checker instantiation

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

static const ModuleItem *FindItemOfKind(const std::vector<ModuleItem *> &items,
                                        ModuleItemKind kind) {
  for (const auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §17.6 Checker instantiation
// =============================================================================
TEST_F(CheckerParseTest, CheckerInstantiatedInModule) {
  auto *unit = Parse(R"(
    checker my_checker(input logic clk, input logic data);
    endchecker

    module top;
      logic clk, data;
      my_checker chk_inst(.clk(clk), .data(data));
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  const auto *inst =
      FindItemOfKind(unit->modules[0]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "my_checker");
  EXPECT_EQ(inst->inst_name, "chk_inst");
}

}  // namespace
