// §11.4.7: Logical operators

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

static Expr *ParseExprFrom(const std::string &src, EvalFixture &f) {
  std::string code = "module t #(parameter P = " + src + ") (); endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  DiagEngine diag(f.mgr);
  Lexer lexer(f.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, f.arena, diag);
  auto *cu = parser.Parse();
  EXPECT_FALSE(cu->modules.empty());
  EXPECT_FALSE(cu->modules[0]->params.empty());
  return cu->modules[0]->params[0].second;
}

namespace {

TEST(ConstEval, Logical) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 0", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 0", f)), 0);
}

TEST(ConstEval, Unary) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("-5", f)), -5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!0", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!5", f)), 0);
}

}  // namespace
