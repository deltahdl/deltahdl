// §11.4.5: Equality operators

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

TEST(ConstEval, Comparison) {
  EvalFixture f;
  struct Case {
    const char *expr;
    int64_t expected;
  };
  const Case kCases[] = {
      {"3 < 5", 1},  {"5 < 3", 0},  {"5 > 3", 1},  {"3 >= 3", 1},
      {"3 <= 3", 1}, {"3 == 3", 1}, {"3 != 4", 1},
  };
  for (const auto &c : kCases) {
    EXPECT_EQ(ConstEvalInt(ParseExprFrom(c.expr, f)), c.expected) << c.expr;
  }
}

}  // namespace
