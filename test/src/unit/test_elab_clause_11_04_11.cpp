// §11.4.11: Conditional operator

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

TEST(ConstEval, Ternary) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? 42 : 99", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 42 : 99", f)), 99);
}

TEST(ConstEval, ScopedTernary) {
  EvalFixture f;
  ScopeMap scope_big = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_big),
            16);
  ScopeMap scope_small = {{"WIDTH", 4}};
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_small), 8);
}

}  // namespace
