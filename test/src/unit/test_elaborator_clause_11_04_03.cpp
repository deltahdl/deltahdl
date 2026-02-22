// §11.4.3: Arithmetic operators

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/const_eval.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include <gtest/gtest.h>

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

TEST(ConstEval, Arithmetic) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 + 4", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("10 - 3", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("6 * 7", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("15 / 3", f)), 5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("17 % 5", f)), 2);
}

TEST(ConstEval, DivisionByZero) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 / 0", f)), std::nullopt);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 % 0", f)), std::nullopt);
}

TEST(ConstEval, Power) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("2 ** 10", f)), 1024);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 ** 0", f)), 1);
}

} // namespace
