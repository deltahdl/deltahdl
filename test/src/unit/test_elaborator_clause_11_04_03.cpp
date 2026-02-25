// §11.4.3: Arithmetic operators

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

struct ElabA83Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA83Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// § expression — binary operations in initial block elaborate
TEST(ElabA83, BinaryExprInInitialElaborates) {
  ElabA83Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial c = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA86Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA86Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// =============================================================================
// A.8.6 Operators — Elaboration
// =============================================================================
// § unary_operator — all unary operators elaborate
TEST(ElabA86, UnaryPlusElaborates) {
  ElabA86Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = +a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, UnaryMinusElaborates) {
  ElabA86Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = -a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § binary_operator — arithmetic operators elaborate
TEST(ElabA86, BinaryAddElaborates) {
  ElabA86Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd3 + 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryDivElaborates) {
  ElabA86Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd20 / 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryModElaborates) {
  ElabA86Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd17 % 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryPowerElaborates) {
  ElabA86Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd2 ** 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
