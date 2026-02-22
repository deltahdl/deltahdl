// §9.2.3: Final procedures

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
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Parse-level fixture
// =============================================================================
struct ProgramTestParse : ::testing::Test {
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
struct ProgramElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSource(const std::string& src,
                                    ProgramElabFixture& f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

static const ModuleItem* FindItemOfKind(const std::vector<ModuleItem*>& items,
                                        ModuleItemKind kind) {
  for (const auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static int CountItemsOfKind(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind) {
  int count = 0;
  for (const auto* item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

namespace {

// =============================================================================
// §24.12 Program with final block
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithFinalBlock) {
  auto* unit = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

}  // namespace
