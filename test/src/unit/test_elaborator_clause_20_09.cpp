// §20.9: Bit vector system functions

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

// ==========================================================================
// §6.8: Implicit signedness of integer types
// ==========================================================================
// ==========================================================================
// §13.4.3 / §20.9: Constant system functions
// ==========================================================================
TEST(ConstEval, Countones) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b10110010)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b11111111)", f)), 8);
}

TEST(ConstEval, Onehot) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00001000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00010010)", f)), 0);
}

TEST(ConstEval, Onehot0) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00010010)", f)), 0);
}

TEST(ConstEval, Clog2) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(5)", f)), 3);
}

}  // namespace
