#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <unordered_set>

#include "builders_ast.h"
#include "builders_sensitivity.h"
#include "common/arena.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_sensitivity_assert.h"
#include "lexer/token.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

bool ReadSignalsContain(const Stmt* body, std::string_view name) {
  std::unordered_set<std::string> reads;
  CollectStmtReads(body, reads);
  return reads.count(std::string(name)) != 0;
}

Stmt* MakeImmediateAssert(Arena& arena, Stmt* pass_stmt, Stmt* fail_stmt) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kAssertImmediate;
  s->assert_expr = SensId(arena, "en");
  s->assert_pass_stmt = pass_stmt;
  s->assert_fail_stmt = fail_stmt;
  return s;
}

Stmt* MakeRandsequence(Arena& arena, Stmt* prod_code, Stmt* weight_code) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kRandsequence;
  RsProd prod;
  prod.kind = RsProdKind::kCodeBlock;
  if (prod_code) prod.code_stmts.push_back(prod_code);
  RsRule rule;
  rule.prods.push_back(prod);
  rule.weight = SensIntLit(arena, 1);
  if (weight_code) rule.weight_code.push_back(weight_code);
  RsProduction production;
  production.name = "top";
  production.rules.push_back(rule);
  s->rs_top_production = "top";
  s->rs_productions.push_back(production);
  return s;
}

TEST(AlwaysCombSensitivityCollection, AssertPassStmtReadNotCollected) {
  Arena arena;
  auto* stmt = MakeImmediateAssert(
      arena, MakeAssign(arena, "y", SensId(arena, "a")), nullptr);

  EXPECT_FALSE(ReadSignalsContain(stmt, "a"));
}

TEST(AlwaysCombSensitivityCollection, AssertFailStmtReadNotCollected) {
  Arena arena;
  auto* stmt = MakeImmediateAssert(arena, nullptr,
                                   MakeAssign(arena, "y", SensId(arena, "b")));

  EXPECT_FALSE(ReadSignalsContain(stmt, "b"));
}

TEST(AlwaysCombSensitivityCollection, RandcaseItemStmtReadCollected) {
  Arena arena;
  auto* stmt = arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.emplace_back(SensIntLit(arena, 1),
                                    MakeAssign(arena, "y", SensId(arena, "c")));

  EXPECT_TRUE(ReadSignalsContain(stmt, "c"));
}

TEST(AlwaysCombSensitivityCollection, RandsequenceCodeBlockReadCollected) {
  Arena arena;
  auto* stmt = MakeRandsequence(
      arena, MakeAssign(arena, "y", SensId(arena, "d")), nullptr);

  EXPECT_TRUE(ReadSignalsContain(stmt, "d"));
}

TEST(AlwaysCombSensitivityInference, RandcaseItemLocalExcluded) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, en, y, z;\n"
      "  always_comb begin\n"
      "    y = a;\n"
      "    randcase\n"
      "      3: begin\n"
      "        logic [7:0] t_local;\n"
      "        z = en + t_local;\n"
      "      end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "en"});
  ExpectSensitivityExcludes(proc, {"t_local"});
}

TEST(AlwaysCombSensitivityCollection, RandsequenceWeightCodeReadCollected) {
  Arena arena;
  auto* stmt = MakeRandsequence(arena, nullptr,
                                MakeAssign(arena, "y", SensId(arena, "e")));

  EXPECT_TRUE(ReadSignalsContain(stmt, "e"));
}

TEST(AlwaysCombSensitivityCollection, VarInitReadsCollected) {
  Arena arena;
  auto* decl = arena.Create<Stmt>();
  decl->kind = StmtKind::kVarDecl;
  decl->var_name = "t";
  decl->var_init = MakeBinary(arena, TokenKind::kPlus, SensId(arena, "a"),
                              SensId(arena, "b"));
  auto* block = arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(decl);
  block->stmts.push_back(MakeAssign(arena, "y", SensId(arena, "t")));

  EXPECT_TRUE(ReadSignalsContain(block, "a"));
  EXPECT_TRUE(ReadSignalsContain(block, "b"));
}

TEST(AlwaysCombSensitivityCollection, RandcaseWeightReadCollected) {
  Arena arena;
  auto* stmt = arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.emplace_back(
      SensId(arena, "w"), MakeAssign(arena, "y", SensIntLit(arena, 1)));

  EXPECT_TRUE(ReadSignalsContain(stmt, "w"));
}

TEST(AlwaysCombSensitivityInference, VarInitFunctionCallReadInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  function automatic logic [7:0] read_a(input logic [7:0] x);\n"
      "    return x + a;\n"
      "  endfunction\n"
      "  always_comb begin\n"
      "    static logic [7:0] tv = read_a(8'd0);\n"
      "    result = tv;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"a"});
}

}  // namespace
