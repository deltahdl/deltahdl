// §9.2.2.2.1 "Implicit always_comb sensitivities", collection side: the cases
// that call CollectStmtReads over a statement built here rather than
// elaborated from source, which is how a position no source reaches easily gets
// covered. The cases that drive the inference end to end are in
// test_elaborator_subclause_09_02_02_02_01a.cpp, which the 1000-line cap in
// .github/workflows/deltahdl.yml separated this file from.

#include <string>
#include <string_view>
#include <unordered_set>

#include "builders_ast.h"
#include "builders_sensitivity.h"
#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_sensitivity_assert.h"

using namespace delta;

namespace {

// True when CollectStmtReads takes `name` from `body`. §9.2.2.2.1 asks which
// names reach the implicit sensitivity list, so the cases below read the
// collected set rather than any diagnostic; a read the walk misses is a wrong
// simulated value and not a missing report.
bool ReadSignalsContain(const Stmt* body, std::string_view name) {
  std::unordered_set<std::string> reads;
  CollectStmtReads(body, reads);
  return reads.count(std::string(name)) != 0;
}

// §16.3 keeps an immediate assertion's action_block statements in
// Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. §9.2.2.2.1 (printed page
// 223) says "Expressions used in assertion action blocks do not contribute to
// the implicit sensitivity list of an always_comb", so a read in either stays
// out of the list.
Stmt* MakeImmediateAssert(Arena& arena, Stmt* pass_stmt, Stmt* fail_stmt) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kAssertImmediate;
  s->assert_expr = SensId(arena, "en");
  s->assert_pass_stmt = pass_stmt;
  s->assert_fail_stmt = fail_stmt;
  return s;
}

// A randsequence statement holds procedural statements in two places: A.6.12
// makes an rs_code_block one form of rs_prod, whose statements the parser puts
// in RsProd::code_stmts, and §18.17.1 lets a weight_specification be followed
// by one, whose statements go in RsRule::weight_code.
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

// §9.2.2.2.1 (printed page 223): "Expressions used in assertion action blocks
// do not contribute to the implicit sensitivity list of an always_comb." These
// two are the collection-level counterpart of
// AlwaysCombSensitivityInference.AssertBothPassAndFailActionsExcluded below,
// and they are what fails if CollectStmtReads is ever handed the whole of
// ForEachChildStmt instead of stopping at the two action-block links.
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

// §18.16 gives a randcase item a statement, which the parser keeps in the
// second member of a Stmt::randcase_items entry. §9.2.2.2.1 names no statement
// position among its exceptions, so a read there belongs in the list.
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

// §9.2.2.2.1 exception (a) leaves out "any expansion of a variable declared
// within the block", and names no statement position, so a variable declared
// in a randcase item's statement is as local as one declared in the enclosing
// sequential block. §18.16 gives that item a statement, which the parser keeps
// in the second member of a Stmt::randcase_items entry.
//
// The case is written over a randcase item rather than an assertion action
// block because printed page 223 keeps action-block reads out of the list
// entirely, so a local declared there could never reach it and a case built on
// one would pass whether exception (a) worked or not. t_local is read and never
// written, so exception (b) cannot remove it and only exception (a) can:
// without CollectBlockLocalNames descending the item, the list carries a name
// no variable of the design answers to.
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

// §9.2.2.2.1 counts every net or variable read within the block, and A.2.4
// gives a variable_decl_assignment an initializer the parser keeps in
// Stmt::var_init. `a` and `b` are read there and nowhere else: neither is
// declared in the block, neither is written in it, and an initializer is not a
// timing control expression, so none of the three exceptions removes them.
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

// §18.16: "The randcase weights can be arbitrary expressions, not just
// constants", each of which the statement evaluates when it runs, so a variable
// named in a weight is read within the block and no exception of §9.2.2.2.1
// removes it. AlwaysCombSensitivityCollection.RandcaseItemStmtReadCollected
// above covers the item's statement, the other member of a
// Stmt::randcase_items entry. The item's assignment here takes a literal so
// that only the weight can supply `w`.
TEST(AlwaysCombSensitivityCollection, RandcaseWeightReadCollected) {
  Arena arena;
  auto* stmt = arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.emplace_back(
      SensId(arena, "w"), MakeAssign(arena, "y", SensIntLit(arena, 1)));

  EXPECT_TRUE(ReadSignalsContain(stmt, "w"));
}

// §9.2.2.2.1 counts a read "within any function called within the block" and
// puts no condition on where in the block the call stands. The only call here
// is in the initializer of a block-local declaration, and it is passed a
// literal, so `a` reaches the list only if CollectCallNamesFromStmt reads
// Stmt::var_init. That is a different walk from the one the two cases above
// pin, and it fails separately.
TEST(AlwaysCombSensitivityInference, VarInitFunctionCallReadInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  function automatic logic [7:0] read_a(input logic [7:0] x);\n"
      "    return x + a;\n"
      "  endfunction\n"
      "  always_comb begin\n"
      "    logic [7:0] tv = read_a(8'd0);\n"
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
