// Non-LRM tests

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/const_eval.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct EvalFixture {
  SourceManager mgr;
  Arena arena;
};

static Expr* ParseExprFrom(const std::string& src, EvalFixture& f) {
  std::string code = "module t #(parameter P = " + src + ") (); endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  DiagEngine diag(f.mgr);
  Lexer lexer(f.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, f.arena, diag);
  auto* cu = parser.Parse();
  EXPECT_FALSE(cu->modules.empty());
  EXPECT_FALSE(cu->modules[0]->params.empty());
  return cu->modules[0]->params[0].second;
}

namespace {

TEST(ConstEval, LongestStaticPrefixSimpleId) {
  Arena arena;
  // Plain identifier "m" → prefix is "m".
  EXPECT_EQ(LongestStaticPrefix(LspId(arena, "m")), "m");
}

TEST(ConstEval, LongestStaticPrefixConstIdx) {
  Arena arena;
  // m[1] where 1 is constant → prefix is "m[1]".
  auto* sel = LspSelect(arena, LspId(arena, "m"), LspInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(sel), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixVarIdx) {
  Arena arena;
  // m[i] where i is not constant → prefix is "m".
  auto* sel = LspSelect(arena, LspId(arena, "m"), LspId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "m");
}

TEST(ConstEval, LongestStaticPrefixNested) {
  Arena arena;
  // m[1][i] → m[1] is static, [i] is not → prefix is "m[1]".
  auto* inner = LspSelect(arena, LspId(arena, "m"), LspInt(arena, 1));
  auto* outer = LspSelect(arena, inner, LspId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(outer), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixParamIdx) {
  Arena arena;
  // m[P] where P=7 in scope → prefix is "m[7]".
  ScopeMap scope = {{"P", 7}};
  auto* sel = LspSelect(arena, LspId(arena, "m"), LspId(arena, "P"));
  EXPECT_EQ(LongestStaticPrefix(sel, scope), "m[7]");
}

}  // namespace
