// §11.4.11: Conditional operator

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;

static std::vector<ModuleItem *>
FindUdpInsts(const std::vector<ModuleItem *> &items) {
  std::vector<ModuleItem *> insts;
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kUdpInst)
      insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem *>
FindContAssigns(const std::vector<ModuleItem *> &items) {
  std::vector<ModuleItem *> result;
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kContAssign)
      result.push_back(item);
  }
  return result;
}

static std::vector<ModuleItem *>
FindItems(const std::vector<ModuleItem *> &items, ModuleItemKind kind) {
  std::vector<ModuleItem *> result;
  for (auto *item : items) {
    if (item->kind == kind)
      result.push_back(item);
  }
  return result;
}

namespace {

TEST(ParserCh505, Operator_Ternary) {
  auto r = Parse("module m;\n"
                 "  initial x = sel ? a : b;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(Eval, Ternary) {
  ExprFixture f;
  auto *expr = ParseExprFrom("1 ? 42 : 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}
// =========================================================================
// Section 11.4.11 -- Conditional operator
// =========================================================================
TEST(ParserSection11, ConditionalTernary) {
  auto r = Parse("module t;\n"
                 "  initial x = (a > b) ? a : b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
} // namespace
