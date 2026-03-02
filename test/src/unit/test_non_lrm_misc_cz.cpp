// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

using SpecifyParseTest = ProgramTestParse;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem* FirstSpecifyBlock(CompilationUnit* cu) {
    for (auto* item : cu->modules[0]->items) {
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

struct ParseResult30 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult30 Parse(const std::string& src) {
  ParseResult30 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection28, Sec28_12_ConditionalFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input a, b, en, output y);\n"
              "  specify\n"
              "    if (en) (a, b *> y) = 10;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// =============================================================================
// §30.3 Path delay declarations
// =============================================================================
TEST_F(SpecifyTest, ParallelPathDelay) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = 5;\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_EQ(cu->modules.size(), 1u);
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(item->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(item->path.src_ports.size(), 1u);
  EXPECT_EQ(item->path.src_ports[0].name, "a");
  ASSERT_EQ(item->path.dst_ports.size(), 1u);
  EXPECT_EQ(item->path.dst_ports[0].name, "b");
  ASSERT_EQ(item->path.delays.size(), 1u);
}

TEST_F(SpecifyTest, FullPathDelay) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a *> b) = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kFull);
}

}  // namespace
