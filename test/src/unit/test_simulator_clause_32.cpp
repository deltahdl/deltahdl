// §32: (MSB) is reserved to represent a file descriptor (fd) returned from the
// SystemVerilog $fopen system

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

// =============================================================================
// §32 SDF annotation (runtime model)
// =============================================================================
TEST_F(SpecifyTest, SdfAnnotateModel) {
  // Test the runtime SpecifyManager SDF annotation support.
  SpecifyManager mgr;
  mgr.AnnotateSdf({"timing.sdf", "top.dut"});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 1u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "timing.sdf");
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].scope, "top.dut");
}

}  // namespace
