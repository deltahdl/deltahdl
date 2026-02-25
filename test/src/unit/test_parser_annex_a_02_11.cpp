// Annex A.2.11: Covergroup declarations

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

TEST(ParserA211, CoverageOption_AutoBinMax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 64;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BlockEventExpression_MultipleOr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin a or begin b or end c);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, HierarchicalBtfIdentifier_Dotted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin top.dut.task1);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
