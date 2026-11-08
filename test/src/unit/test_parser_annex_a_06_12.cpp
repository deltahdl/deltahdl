#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(RandsequenceSyntaxParsing, RandsequenceWithName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { $display(\"first\"); };\n"
      "      second : { $display(\"second\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
  EXPECT_EQ(stmt->rs_top_production, "main");
}

TEST(RandsequenceSyntaxParsing, RandsequenceNoName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      main : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
  EXPECT_TRUE(stmt->rs_top_production.empty());
}

TEST(RandsequenceSyntaxParsing, RsProductionMultipleProds) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a b c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsRuleAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a | b | c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsWeightSpecification) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 3 | b := 7;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsCodeBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { int x; x = 5; $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsRepeat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(3) step;\n"
      "      step : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (sel)\n"
      "        0: a;\n"
      "        1: b;\n"
      "        default: c;\n"
      "      endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsRandJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join a b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsWeightWithCodeBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 5 { $display(\"chose a\"); }\n"
      "           | b := 5 { $display(\"chose b\"); };\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, NestedRandsequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(outer)\n"
      "      outer : {\n"
      "        randsequence(inner)\n"
      "          inner : { ; };\n"
      "        endsequence\n"
      "      };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, ComplexMixedProds) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(2) step { $display(\"done\"); };\n"
      "      step : if (1) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsProdAsProductionItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsWeightIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  int w = 5;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := w | b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsWeightParenExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := (2 + 3) | b := (1);\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsIfOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsCaseItemDefaultColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0)\n"
      "               default : a;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsCaseItemCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (1)\n"
      "               0, 1: a;\n"
      "               2, 3: b;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsProductionListRandJoinWithExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join (1) a b c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsProductionWithReturnType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      int main : gen;\n"
      "      gen : { return 42; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsProductionWithPorts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(5);\n"
      "      void gen(int x) : { $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, RsProductionItemWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(1, 2);\n"
      "      void gen(int a, int b) : { $display(a + b); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, EmptyCodeBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, CaseDefaultWithoutColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0)\n"
      "               default a;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, ProductionItemEmptyArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen();\n"
      "      void gen : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, EmptyRandsequenceBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a randsequence statement holds at least one production", 4,
      "A.6.12"));
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
  EXPECT_TRUE(stmt->rs_productions.empty());
}

TEST(RandsequenceSyntaxParsing, MissingEndsequenceErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { ; };\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'end'", 5, "18.17"));
}

TEST(RandsequenceSyntaxParsing, MissingColonInProductionErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ':', got '{'", 4, "18.17"));
}

TEST(RandsequenceSyntaxParsing, MissingSemicolonInProductionErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { ; }\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endsequence'", 5, "18.17"));
}

TEST(RandsequenceSyntaxParsing, RandJoinSingleItemErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join a;\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 4, "18.17"));
}

TEST(RandsequenceSyntaxParsing, CodeBlockDeclaresDataOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence (main)\n"
      "      main : { localparam int L = 1; $display(L); };\n"
      "    endsequence\n"
      "    randsequence (top)\n"
      "      top : { parameter int P = 2; $display(P); };\n"
      "    endsequence\n"
      "    randsequence (go)\n"
      "      go : { let twice(a) = 2 * a; $display(twice(3)); };\n"
      "    endsequence\n"
      "    randsequence (ok)\n"
      "      ok : { int i = 4; typedef bit t; t j; $display(i, j); };\n"
      "    endsequence\n"
      "    randsequence (w)\n"
      "      w : a := 2 { localparam int W = 1; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  const char* msg =
      "a randsequence code block declares data, never a parameter or a let";
  for (uint32_t line : {4U, 7U, 10U, 16U}) {
    EXPECT_TRUE(ReportedError(r.diags, msg, line, "A.6.12"));
  }
  EXPECT_FALSE(ReportedError(r.diags, msg, 13, "A.6.12"));
}

TEST(RandsequenceSyntaxParsing, CodeBlockDeclarationAfterAStatementIsReported) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence (main)\n"
      "      main : {\n"
      "        int a = 1;\n"
      "        $display(a);\n"
      "        int b = 2;\n"
      "        $display(b);\n"
      "      };\n"
      "    endsequence\n"
      "    randsequence (top)\n"
      "      top : {\n"
      "        ;\n"
      "        int c = 3;\n"
      "        $display(c);\n"
      "      };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  const char* msg =
      "a declaration cannot follow a statement in a randsequence code block";
  for (uint32_t line : {7U, 14U}) {
    EXPECT_TRUE(ReportedError(r.diags, msg, line, "A.6.12"));
  }
  EXPECT_FALSE(ReportedError(r.diags, msg, 5, "A.6.12"));
}

TEST(RandsequenceSyntaxParsing, WeightFormsWithoutParenthesesAccepted) {
  auto r = Parse(
      "module m;\n"
      "  int w;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 2 | a := 4'd3 | a := w | a := p::w | a := $unit::w\n"
      "           | a := (w + 1) | a := (top.w);\n"
      "      a : { };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(RandsequenceSyntaxParsing, OtherWeightFormsWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  int w[2];\n"
      "  initial randsequence(main)\n"
      "    main : a := 1.5\n"
      "         | a := w[0]\n"
      "         | a := f(1)\n"
      "         | a := top.w\n"
      "         | a := $root.w\n"
      "         | a := p::q::w\n"
      "         | a := $unit::p::w\n"
      "         | a := $\n"
      "         | a := null\n"
      "         | a := '1\n"
      "         ;\n"
      "    a : { };\n"
      "  endsequence\n"
      "endmodule\n");
  for (uint32_t line = 4; line <= 13; ++line) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a rule's weight written without parentheses is "
                              "an integral number or an identifier, which a "
                              "package scope may qualify; any other expression "
                              "is parenthesized",
                              line, "A.6.12"))
        << "line " << line;
  }
}

TEST(RandsequenceSyntaxParsing, RandsequenceWithNoProductionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial randsequence()\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a randsequence statement holds at least one production", 3,
      "A.6.12"));
}

TEST(RandsequenceSyntaxParsing, CaseProductionWithNoItemRejected) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial randsequence(main)\n"
      "    main : case (x)\n"
      "           endcase;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a case production holds at least one item", 5, "A.6.12"));
}

TEST(RandsequenceSyntaxParsing, ProductionWithEmptyParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial randsequence(main)\n"
      "    main : p q;\n"
      "    p() : { $display(\"p\"); };\n"
      "    q(int a = 1) : { $display(a); };\n"
      "  endsequence\n"
      "endmodule\n");
  const char* msg =
      "a production's parentheses enclose at least one formal argument; a "
      "production with none is written without them";
  EXPECT_TRUE(ReportedError(r.diags, msg, 4, "A.6.12"));
  EXPECT_FALSE(ReportedError(r.diags, msg, 5, "A.6.12"));
}

TEST(RandsequenceSyntaxParsing, ProductionItemArgumentsByNameAndOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : p(1, ) p(, 2) p(.b(), .a(3)) p(4, .b(5));\n"
      "      void p(int a = 0, int b = 7) : { };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const Stmt* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->kind, StmtKind::kRandsequence);
  const auto& prods = stmt->rs_productions[0].rules[0].prods;
  ASSERT_EQ(prods.size(), 4u);
  const RsProductionItem& trailing_empty = prods[0].item;
  ASSERT_EQ(trailing_empty.args.size(), 2u);
  EXPECT_NE(trailing_empty.args[0], nullptr);
  EXPECT_EQ(trailing_empty.args[1], nullptr);
  EXPECT_TRUE(trailing_empty.arg_names.empty());
  const RsProductionItem& leading_empty = prods[1].item;
  ASSERT_EQ(leading_empty.args.size(), 2u);
  EXPECT_EQ(leading_empty.args[0], nullptr);
  EXPECT_NE(leading_empty.args[1], nullptr);
  const RsProductionItem& named = prods[2].item;
  ASSERT_EQ(named.args.size(), 2u);
  ASSERT_EQ(named.arg_names.size(), 2u);
  EXPECT_EQ(named.arg_names[0], "b");
  EXPECT_EQ(named.args[0], nullptr);
  EXPECT_EQ(named.arg_names[1], "a");
  EXPECT_NE(named.args[1], nullptr);
  const RsProductionItem& mixed = prods[3].item;
  ASSERT_EQ(mixed.args.size(), 2u);
  ASSERT_EQ(mixed.arg_names.size(), 1u);
  EXPECT_EQ(mixed.arg_names[0], "b");
}

TEST(RandsequenceSyntaxParsing, ProductionItemDefaultArgumentRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial randsequence(main)\n"
      "    main : p(default);\n"
      "    p(int a = 0) : { };\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got 'default'", 3, "18.17.7"));
}

}  // namespace
