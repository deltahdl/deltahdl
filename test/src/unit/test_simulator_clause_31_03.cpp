// §31.3: Timing checks using a stability window

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/specify.h"

using namespace delta;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit *Parse(const std::string &src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem *FirstSpecifyBlock(CompilationUnit *cu) {
    for (auto *item : cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
    }
    return nullptr;
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

namespace {

TEST_F(SpecifyTest, RuntimeTimingCheckSetupViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);

  // data_time=95, ref_time=100: gap=5 < 10 => violation
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 95));
  // data_time=85, ref_time=100: gap=15 >= 10 => no violation
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 85));
}

TEST_F(SpecifyTest, RuntimeTimingCheckHoldViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);

  // ref_time=100, data_time=103: gap=3 < 5 => violation
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 103));
  // ref_time=100, data_time=110: gap=10 >= 5 => no violation
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 110));
}

}  // namespace
