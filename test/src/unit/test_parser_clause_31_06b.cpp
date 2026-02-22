// §31.6: Notifiers: user-defined responses to timing violations

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/specify.h"
#include <gtest/gtest.h>

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
      if (item->kind == ModuleItemKind::kSpecifyBlock)
        return item;
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

TEST_F(SpecifyTest, TimingCheckWithNotifier) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  $setup(data, posedge clk, 10, ntfr);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.notifier, "ntfr");
}

TEST_F(SpecifyTest, TimeskewWithNotifier) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  $timeskew(posedge clk1, posedge clk2, 5, ntfr);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.notifier, "ntfr");
}

} // namespace
