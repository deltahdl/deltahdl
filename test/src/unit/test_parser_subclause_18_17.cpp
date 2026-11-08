#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

const RsProduction* FindProd(const Stmt* stmt, std::string_view name) {
  for (const auto& p : stmt->rs_productions) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

const Stmt* RandseqStmt(ParseResult& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->kind == StmtKind::kRandsequence ? stmt : nullptr;
}

TEST(RandseqBaseParse, RandsequenceStatementCapturesTopAndProductions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a ;\n"
      "      a : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rs_top_production, "main");
  ASSERT_EQ(stmt->rs_productions.size(), 2u);
  EXPECT_EQ(stmt->rs_productions[0].name, "main");
  EXPECT_EQ(stmt->rs_productions[1].name, "a");
}

TEST(RandseqBaseParse, OmittedTopProductionNameLeavesEntryUnset) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      only : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->rs_top_production.empty());
  ASSERT_EQ(stmt->rs_productions.size(), 1u);
  EXPECT_EQ(stmt->rs_productions[0].name, "only");
}

TEST(RandseqBaseParse, ProductionListSequencesMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a b c ;\n"
      "      a : { ; } ;\n"
      "      b : { ; } ;\n"
      "      c : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* main = FindProd(stmt, "main");
  ASSERT_NE(main, nullptr);
  ASSERT_EQ(main->rules.size(), 1u);
  const auto& prods = main->rules[0].prods;
  ASSERT_EQ(prods.size(), 3u);
  EXPECT_EQ(prods[0].kind, RsProdKind::kItem);
  EXPECT_EQ(prods[0].item.name, "a");
  EXPECT_TRUE(prods[0].item.args.empty());
  EXPECT_EQ(prods[1].item.name, "b");
  EXPECT_EQ(prods[2].item.name, "c");
}

TEST(RandseqBaseParse, ProductionOffersAlternativeRulesSeparatedByPipe) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a | b ;\n"
      "      a : { ; } ;\n"
      "      b : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* main = FindProd(stmt, "main");
  ASSERT_NE(main, nullptr);
  ASSERT_EQ(main->rules.size(), 2u);
  ASSERT_EQ(main->rules[0].prods.size(), 1u);
  EXPECT_EQ(main->rules[0].prods[0].item.name, "a");
  ASSERT_EQ(main->rules[1].prods.size(), 1u);
  EXPECT_EQ(main->rules[1].prods[0].item.name, "b");
}

TEST(RandseqBaseParse, CodeBlockProductionParsesAsTerminal) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    randsequence(term)\n"
      "      term : { x = 8'd1; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* term = FindProd(stmt, "term");
  ASSERT_NE(term, nullptr);
  ASSERT_EQ(term->rules.size(), 1u);
  ASSERT_EQ(term->rules[0].prods.size(), 1u);
  EXPECT_EQ(term->rules[0].prods[0].kind, RsProdKind::kCodeBlock);
  EXPECT_FALSE(term->rules[0].prods[0].code_stmts.empty());
}

TEST(RandseqBaseParse, CodeBlockCapturesDataDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(term)\n"
      "      term : { int v; v = 8'd7; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* term = FindProd(stmt, "term");
  ASSERT_NE(term, nullptr);
  ASSERT_EQ(term->rules.size(), 1u);
  ASSERT_EQ(term->rules[0].prods.size(), 1u);
  const auto& prod = term->rules[0].prods[0];
  EXPECT_EQ(prod.kind, RsProdKind::kCodeBlock);
  bool has_var_decl = false;
  for (auto* s : prod.code_stmts) {
    if (s->kind == StmtKind::kVarDecl && s->var_name == "v")
      has_var_decl = true;
  }
  EXPECT_TRUE(has_var_decl);
}

TEST(RandseqBaseParse, MissingEndsequenceIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a ;\n"
      "      a : { ; } ;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'end'", 6, "18.17"));
}

TEST(RandseqBaseParse, MalformedProductionNames18_17) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence (main)\n"
      "      main add;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ':'", 4, "18.17"));
}

TEST(RandseqBaseParse, TypeNameBeforeProductionIdentifierIsNotTheName) {
  auto r = Parse(
      "module m;\n"
      "  typedef int word;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      void main : v ;\n"
      "      word v : { return 7; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->rs_productions.size(), 2u);
  EXPECT_EQ(stmt->rs_productions[1].name, "v");
  EXPECT_EQ(FindProd(stmt, "word"), nullptr);
}

TEST(RandseqBaseParse, ProductionItemCarriesTheLineOfTheNameItUses) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a ;\n"
      "      a : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* main = FindProd(stmt, "main");
  ASSERT_NE(main, nullptr);
  ASSERT_EQ(main->rules.size(), 1u);
  ASSERT_EQ(main->rules[0].prods.size(), 1u);
  EXPECT_EQ(main->rules[0].prods[0].item.loc.line, 4u);
}

}  // namespace
