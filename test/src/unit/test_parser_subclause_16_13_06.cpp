#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// §16.13.6: the actual for a formal of type sequence in an instance a
// sequence body holds, the clause's `e2_with_arg(@(posedge sysclk) $rose(a)
// ##1 b ##1 c)`, is read as a sequence carried by the identifier standing
// in the argument's place, with the clock it opens with.
TEST(SequenceMethodParsing, ASequenceActualInASequenceBodyIsReadAsASequence) {
  auto r = Parse(
      "module m;\n"
      "  sequence e2_with_arg(sequence subseq);\n"
      "    @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 "
      "branch_back;\n"
      "  endsequence\n"
      "  sequence e4;\n"
      "    e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* e4 = nullptr;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "e4") {
      e4 = item;
    }
  }
  ASSERT_NE(e4, nullptr);
  ASSERT_EQ(e4->seq_linear.operands.size(), 1u);
  const Expr* instance = e4->seq_linear.operands[0];
  EXPECT_EQ(instance->kind, ExprKind::kCall);
  ASSERT_EQ(instance->args.size(), 1u);
  const PropertyExprNode* actual = instance->args[0]->property_actual;
  ASSERT_NE(actual, nullptr);
  EXPECT_EQ(actual->kind, PropertyExprNode::Kind::kSequence);
  ASSERT_NE(actual->sequence, nullptr);
  EXPECT_EQ(actual->sequence->seq_linear.operands.size(), 3u);
  ASSERT_EQ(actual->clock.size(), 1u);
  EXPECT_EQ(actual->clock[0].signal->text, "sysclk");
}

// §16.13.6: an actual that is an expression, `e2_with_arg(ready)`, is kept
// as the expression it is.
TEST(SequenceMethodParsing, AnExpressionActualInASequenceBodyStaysOne) {
  auto r = Parse(
      "module m;\n"
      "  sequence e2_with_arg(sequence subseq);\n"
      "    @(posedge sysclk) reset ##1 subseq.triggered;\n"
      "  endsequence\n"
      "  sequence e4;\n"
      "    e2_with_arg(ready);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* e4 = nullptr;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "e4") {
      e4 = item;
    }
  }
  ASSERT_NE(e4, nullptr);
  ASSERT_EQ(e4->seq_linear.operands.size(), 1u);
  ASSERT_EQ(e4->seq_linear.operands[0]->args.size(), 1u);
  const Expr* actual = e4->seq_linear.operands[0]->args[0];
  EXPECT_EQ(actual->property_actual, nullptr);
  EXPECT_EQ(actual->text, "ready");
}

}  // namespace
