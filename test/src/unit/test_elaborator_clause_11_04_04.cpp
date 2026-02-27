// §11.4.4: Relational operators

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Comparison) {
  EvalFixture f;
  struct Case {
    const char* expr;
    int64_t expected;
  };
  const Case kCases[] = {
      {"3 < 5", 1},  {"5 < 3", 0},  {"5 > 3", 1},  {"3 >= 3", 1},
      {"3 <= 3", 1}, {"3 == 3", 1}, {"3 != 4", 1},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(ConstEvalInt(ParseExprFrom(c.expr, f)), c.expected) << c.expr;
  }
}

}  // namespace
