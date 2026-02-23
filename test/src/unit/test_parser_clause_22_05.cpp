#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

TEST(ParserSection22, DefineSimpleMacro) {
  EXPECT_TRUE(
      ParseOk("`define WIDTH 8\n"
              "module t;\n"
              "  logic [`WIDTH-1:0] data;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefineAndUndef) {
  EXPECT_TRUE(
      ParseOk("`define FOO 1\n"
              "module t;\n"
              "endmodule\n"
              "`undef FOO\n"));
}

TEST(ParserSection22, UndefineallDirective) {
  EXPECT_TRUE(
      ParseOk("`define A 1\n"
              "`define B 2\n"
              "`undefineall\n"
              "module t;\n"
              "endmodule\n"));
}
struct ParseResult313 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult313 Parse(const std::string &src) {
  ParseResult313 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool HasItemOfKindAndName(const std::vector<ModuleItem *> &items,
                                 ModuleItemKind kind, const std::string &name) {
  for (const auto *item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

static bool HasAttrNamed(const std::vector<ModuleItem *> &items,
                         const std::string &name) {
  for (const auto *item : items)
    for (const auto &attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

// 31. Text macro name space (d) — `define introduces names with leading `
TEST(ParserClause03, Cl3_13_TextMacroNameSpace) {
  // Macro defined and used; subsequent redefinition overrides previous
  auto r = Parse(
      "`define WIDTH 8\n"
      "`define DEPTH 16\n"
      "module m;\n"
      "  logic [`WIDTH-1:0] data;\n"
      "  logic [`DEPTH-1:0] addr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Macro names are unambiguous with other name spaces (leading ` character)
  EXPECT_TRUE(
      ParseOk("`define data 42\n"
              "module m; logic [7:0] data; endmodule\n"));
}

