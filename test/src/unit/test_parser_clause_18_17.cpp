#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §18.17 owns the base randsequence grammar of Syntax 18-13: the
// randsequence_statement itself, a production's rule list, a production list of
// sequenced items, the code-block terminal, and the bare production item.
// (Return types and formal arguments belong to §18.17.7; weights to §18.17.1;
// if/repeat/case/rand join to §18.17.2-.5.) These parser tests observe that the
// production carried by parser_verify.cpp captures each base form into the AST.

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

// §18.17 (randsequence_statement): the block parses to a randsequence statement
// whose optional production name after the keyword designates the top-level
// production, and whose body productions are all captured in declaration order.
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

// §18.17 (randsequence_statement): the top-production name inside the
// parentheses is optional. When it is omitted the parser leaves the recorded
// top-production name empty; selecting the first production as the entry is a
// runtime concern observed by the simulator, not the parser.
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

// §18.17 (rs_production_list ::= rs_prod { rs_prod }, rs_prod ::=
// rs_production_item, rs_production_item ::= rs_production_identifier): a
// production list holds a succession of production items. Each is captured as a
// bare item (no argument list) in written order.
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

// §18.17 (rs_production ::= ... rs_rule { | rs_rule }): a single production may
// contain multiple rule alternatives separated by '|', which the standard
// describes as a set of random choices. The parser records one RsRule per
// alternative.
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

// §18.17 (rs_prod ::= rs_code_block, rs_code_block ::= { ... }): a code block
// is a terminal production item that needs no further definition than its
// statements. The parser records it as a code-block RsProd carrying the block's
// statements rather than a named production reference.
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

// §18.17 (rs_code_block ::= { {data_declaration} {statement_or_null} }): a code
// block may open with data declarations ahead of its statements. The parser
// records a variable declared inside the block in the block's statement list
// (as a variable declaration), exercising the data-declaration part of the
// grammar rather than the plain statement part.
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

// §18.17 (randsequence_statement ::= randsequence ( ... ) rs_production
// { rs_production } endsequence, NEGATIVE): the block must be closed with the
// endsequence keyword. A randsequence whose productions run into the enclosing
// block's end without an endsequence is rejected.
TEST(RandseqBaseParse, MissingEndsequenceIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a ;\n"
      "      a : { ; } ;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
