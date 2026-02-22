// §9.2.3: Final procedures

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

using namespace delta;

// =============================================================================
// Parse-level fixture
// =============================================================================
struct ProgramTestParse : ::testing::Test {
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
struct ProgramElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

namespace {

// =============================================================================
// §24.12 Program with final block
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithFinalBlock) {
  auto *unit = Parse("program p;\n"
                     "  final begin\n"
                     "    $display(\"done\");\n"
                     "  end\n"
                     "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

} // namespace
