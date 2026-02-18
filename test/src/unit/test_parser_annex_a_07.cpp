#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

}  // namespace

// =============================================================================
// A.7 -- Specify section
// =============================================================================

TEST(ParserAnnexA, A7SpecifyParallelPath) {
  auto r = Parse("module m; specify (a => b) = 5; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecifyBlock);
  ASSERT_GE(r.cu->modules[0]->items[0]->specify_items.size(), 1u);
}

TEST(ParserAnnexA, A7SpecifyFullPath) {
  auto r =
      Parse("module m; specify (a, b *> c, d) = 10; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7TimingCheckSetup) {
  auto r = Parse(
      "module m;\n"
      "  specify $setup(data, posedge clk, 10); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7TimingCheckHold) {
  auto r = Parse(
      "module m;\n"
      "  specify $hold(posedge clk, data, 5); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7SpecparamInSpecify) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRISE = 100;\n"
      "    (a => b) = tRISE;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
