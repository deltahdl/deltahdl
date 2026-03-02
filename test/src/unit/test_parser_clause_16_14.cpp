// §16.14: Concurrent assertions

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string& src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static size_t CountItemsByKind(const std::vector<ModuleItem*>& items,
                               ModuleItemKind kind) {
  size_t count = 0;
  for (auto* item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

using VerifyParseTest = ProgramTestParse;

namespace {

// =============================================================================
// Section 16.5.1 -- Multiple concurrent assertions in same module
// =============================================================================
// Multiple assert/assume/cover property items in one module.
TEST(ParserSection16, Sec16_5_1_MultipleConcurrentAssertions) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "  assume property (@(posedge clk) en);\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssertProperty),
            1u);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssumeProperty),
            1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      1u);
}

}  // namespace
