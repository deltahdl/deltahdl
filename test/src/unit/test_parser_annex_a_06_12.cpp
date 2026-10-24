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
      "      void gen() : { ; };\n"
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
  // Without endsequence the enclosing end reaches the production list, where
  // §18.17 reports it as a missing production identifier.
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
  // The endsequence keyword stands where §18.17 requires the production's ';'.
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
  // rand join takes two production items, so the ';' after the first stands
  // where §18.17 requires the second one's identifier.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 4, "18.17"));
}

// rs_code_block ::= { { data_declaration } { statement_or_null } }, so of
// A.2.8's block item declarations a code block takes the data_declarations
// alone: a localparam, a parameter or a let is reported, in a production's
// code block and in a weight's, while a variable, a typedef and a variable of
// the typedef's type are not.
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

// A code block's data_declarations all come before its first
// statement_or_null, so a declaration after a statement, or after a null
// statement, is reported, and the one opening a code block is not.
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

}  // namespace
