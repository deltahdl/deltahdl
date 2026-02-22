// §30.4: Module path declarations

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

// =============================================================================
// §30.3 Path delay declarations
// =============================================================================
TEST_F(SpecifyTest, ParallelPathDelay) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  (a => b) = 5;\n"
                   "endspecify\n"
                   "endmodule\n");
  ASSERT_EQ(cu->modules.size(), 1u);
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(item->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(item->path.src_ports.size(), 1u);
  EXPECT_EQ(item->path.src_ports[0].name, "a");
  ASSERT_EQ(item->path.dst_ports.size(), 1u);
  EXPECT_EQ(item->path.dst_ports[0].name, "b");
  ASSERT_EQ(item->path.delays.size(), 1u);
}

TEST_F(SpecifyTest, FullPathDelay) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  (a *> b) = 10;\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kFull);
}

// =============================================================================
// §30.3.1 Edge-sensitive paths
// =============================================================================
TEST_F(SpecifyTest, PosedgePath) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  (posedge clk => q) = 10;\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto *path = spec->specify_items[0];
  EXPECT_EQ(path->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(path->path.src_ports[0].name, "clk");
  EXPECT_EQ(path->path.dst_ports[0].name, "q");
}

TEST_F(SpecifyTest, NegedgePath) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  (negedge clk => q) = 8;\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->path.edge, SpecifyEdge::kNegedge);
}

} // namespace
