// §19.5: Defining coverage points

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
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.11 Production #4: coverage_spec
// =============================================================================
TEST(ParserA211, CoverageSpec_CoverPoint) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint addr;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #8: cover_point
// =============================================================================
TEST(ParserA211, CoverPoint_BasicExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint addr;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint addr iff (enable);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_LabeledWithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    my_cp: coverpoint data iff (valid);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_ComplexExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint (a + b);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrEmpty_EmptyBraces) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {}\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
