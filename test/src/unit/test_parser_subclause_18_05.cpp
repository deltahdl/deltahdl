#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

TEST(ConstraintSideEffect, IncrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == y++; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, DecrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == y--; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, PrefixIncrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { ++x < 10; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, PrefixDecrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { --x < 10; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, PlainArithmeticAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { x == y + 1; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistNesting, TopLevelDistAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1:=1, 2:=3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistNesting, DistInIfBranchAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand bit a;\n"
      "  constraint c { if (a) x dist {1:=1, 2:=3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistNesting, DistInsideParenthesizedOperandRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { y == (x dist {1:=1, 2:=3}); }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a dist expression may not appear within another expression", 4,
      "18.5"));
}

TEST(ConstraintDistNesting, DistFollowedByOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { x dist {1:=1} + y; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a dist expression may not appear within another expression", 4,
      "18.5"));
}

TEST(ConstraintDistNesting, DistAsImplicationAntecedentRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { x dist {1:=1} -> y > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a dist expression may not appear within another expression", 4,
      "18.5"));
}

TEST(ConstraintBlock, MalformedConstraintNames18_5) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint { x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier", 3, "18.5"));
}

constexpr std::string_view kSideEffect =
    "operator with side effects is not allowed in a constraint";
constexpr std::string_view kDistNested =
    "a dist expression may not appear within another expression";

constexpr uint32_t kClassItemLine = 6;
constexpr uint32_t kExternalItemLine = 7;
constexpr uint32_t kInlineItemLine = 9;
constexpr uint32_t kScopeItemLine = 5;

std::string InClass(std::string_view item) {
  return std::string(
             "class C;\n"
             "  rand int x, a[4];\n"
             "  rand bit b;\n"
             "  int y;\n"
             "  function int f(int v); return v; endfunction\n"
             "  constraint c { ") +
         std::string(item) +
         " }\n"
         "endclass\n";
}

std::string InExternal(std::string_view item) {
  return std::string(
             "class C;\n"
             "  rand int x, a[4];\n"
             "  rand bit b;\n"
             "  int y;\n"
             "  extern constraint c;\n"
             "endclass\n"
             "constraint C::c { ") +
         std::string(item) + " }\n";
}

std::string InInline(std::string_view item) {
  return std::string(
             "class C;\n"
             "  rand int x, a[4];\n"
             "  rand bit b;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic C o = new;\n"
             "    automatic int z = 0;\n"
             "    void'(o.randomize() with { ") +
         std::string(item) +
         " });\n"
         "  end\n"
         "endmodule\n";
}

std::string InScope(std::string_view item) {
  return std::string(
             "module m;\n"
             "  initial begin\n"
             "    automatic int x = 0, z = 0;\n"
             "    automatic bit b;\n"
             "    void'(std::randomize(x, b) with { ") +
         std::string(item) +
         " });\n"
         "  end\n"
         "endmodule\n";
}

void ExpectReported(const std::string& src, std::string_view message,
                    uint32_t line) {
  auto r = Parse(src);
  EXPECT_TRUE(ReportedError(r.diags, message, line, "18.5")) << src;
}

void ExpectAccepted(const std::string& src) {
  auto r = Parse(src);
  EXPECT_FALSE(r.has_errors) << src;
}

TEST(ConstraintSideEffect, IncrementInAnExternalBlockRejected) {
  ExpectReported(InExternal("x == y++;"), kSideEffect, kExternalItemLine);
}

TEST(ConstraintSideEffect, PlainArithmeticInAnExternalBlockAccepted) {
  ExpectAccepted(InExternal("x == y + 1;"));
}

TEST(ConstraintSideEffect, IncrementAndDecrementInAnInlineBlockRejected) {
  ExpectReported(InInline("x == z++;"), kSideEffect, kInlineItemLine);
  ExpectReported(InInline("x == --z;"), kSideEffect, kInlineItemLine);
}

TEST(ConstraintSideEffect, PlainArithmeticInAnInlineBlockAccepted) {
  ExpectAccepted(InInline("x == z + 1;"));
}

TEST(ConstraintSideEffect, IncrementInAScopeRandomizeBlockRejected) {
  ExpectReported(InScope("x == z++;"), kSideEffect, kScopeItemLine);
}

TEST(ConstraintSideEffect, PlainArithmeticInAScopeRandomizeBlockAccepted) {
  ExpectAccepted(InScope("x == z + 1;"));
}

TEST(ConstraintSideEffect, IncrementInEveryNestedConstraintFormRejected) {
  for (std::string_view item :
       {"if (b) x == y++;", "if (b) x == 1; else x == y++;", "b -> x == y++;",
        "foreach (a[i]) a[i] == y++;", "soft x == y++;", "x dist {y++ := 1};",
        "x dist {1 := y++};"}) {
    ExpectReported(InClass(item), kSideEffect, kClassItemLine);
  }
}

TEST(ConstraintSideEffect, EveryNestedConstraintFormWithoutOneAccepted) {
  for (std::string_view item :
       {"if (b) x == y + 1;", "if (b) x == 1; else x == y + 1;",
        "b -> x == y + 1;", "foreach (a[i]) a[i] == y + 1;", "soft x == y + 1;",
        "x dist {y + 1 := 1};"}) {
    ExpectAccepted(InClass(item));
  }
}

TEST(ConstraintSideEffect, IncrementAsAFunctionArgumentRejected) {
  ExpectReported(InClass("x == f(y++);"), kSideEffect, kClassItemLine);
}

TEST(ConstraintSideEffect, PlainFunctionArgumentAccepted) {
  ExpectAccepted(InClass("x == f(y + 1);"));
}

TEST(ConstraintSideEffect, DISABLED_AssignmentInAClassBlockRejected) {
  ExpectReported(InClass("x == (y = 3);"), kSideEffect, kClassItemLine);
}

TEST(ConstraintSideEffect, EqualityInAClassBlockAccepted) {
  ExpectAccepted(InClass("x == (y == 3);"));
}

TEST(ConstraintSideEffect,
     DISABLED_EveryCompoundAssignmentInAClassBlockRejected) {
  for (std::string_view op : {"+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
                              "<<=", ">>=", "<<<=", ">>>="}) {
    ExpectReported(InClass("x == (y " + std::string(op) + " 3);"), kSideEffect,
                   kClassItemLine);
  }
}

TEST(ConstraintSideEffect, DISABLED_AssignmentInAnInlineBlockRejected) {
  ExpectReported(InInline("x == (z = 4);"), kSideEffect, kInlineItemLine);
}

TEST(ConstraintSideEffect, DISABLED_AssignmentInAnExternalBlockRejected) {
  ExpectReported(InExternal("x == (y = 3);"), kSideEffect, kExternalItemLine);
}

TEST(ConstraintSideEffect, DISABLED_AssignmentInAScopeRandomizeBlockRejected) {
  ExpectReported(InScope("x == (z = 4);"), kSideEffect, kScopeItemLine);
}

TEST(ConstraintDistNesting, DistAsAnOperandOfAnyOperatorRejected) {
  for (std::string_view item :
       {"!(x dist {1:=1});", "(x dist {1:=1}) && b;",
        "b ? x dist {1:=1} : x == 2;", "x dist {1:=1} dist {2:=1};",
        "(x dist {1:=1});"}) {
    ExpectReported(InClass(item), kDistNested, kClassItemLine);
  }
}

TEST(ConstraintDistNesting, DistAsAnIfConditionRejected) {
  ExpectReported(InClass("if (x dist {1:=1}) b == 1;"), kDistNested,
                 kClassItemLine);
}

TEST(ConstraintDistNesting, DistAsAnOperandInAForeachBodyRejected) {
  ExpectReported(InClass("foreach (a[i]) a[i] dist {1:=1} + 1 == 2;"),
                 kDistNested, kClassItemLine);
}

TEST(ConstraintDistNesting, DistAsAWholeConstraintInEveryFormAccepted) {
  for (std::string_view item :
       {"b -> x dist {1:=1, 2:=1};", "foreach (a[i]) a[i] dist {1:=1};",
        "soft x dist {1:=1};", "if (b) x dist {1:=1}; else x dist {2:=1};"}) {
    ExpectAccepted(InClass(item));
  }
}

TEST(ConstraintDistNesting, DistAsAnOperandInAnExternalBlockRejected) {
  ExpectReported(InExternal("b == (x dist {1:=1});"), kDistNested,
                 kExternalItemLine);
}

TEST(ConstraintDistNesting, DistAsAnOperandInAnInlineBlockRejected) {
  ExpectReported(InInline("b == (x dist {1:=1});"), kDistNested,
                 kInlineItemLine);
}

TEST(ConstraintDistNesting, DistAsAnOperandInAScopeRandomizeBlockRejected) {
  ExpectReported(InScope("b == (x dist {1:=1});"), kDistNested, kScopeItemLine);
}

TEST(ConstraintDistNesting, DistAsAWholeConstraintOutsideAClassAccepted) {
  ExpectAccepted(InExternal("x dist {1:=1, 2:=1};"));
  ExpectAccepted(InInline("x dist {1:=1, 2:=1};"));
  ExpectAccepted(InScope("x dist {1:=1, 2:=1};"));
}

const ClassMember* BlockOf(const ParseResult& r) {
  if (r.cu == nullptr || r.cu->classes.empty()) return nullptr;
  for (const ClassMember* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint) return m;
  }
  return nullptr;
}

std::vector<ConstraintItemKind> KindsOf(
    const std::vector<ConstraintItem*>& items) {
  std::vector<ConstraintItemKind> kinds;
  kinds.reserve(items.size());
  for (const ConstraintItem* item : items) kinds.push_back(item->kind);
  return kinds;
}

TEST(ConstraintItems, ABlockKeepsItsItemsInSourceOrder) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { solve a before b; x dist {1 := 2, [3:4] :/ 1};\n"
      "                 unique {a, b}; a < b; soft x > 1; disable soft x; }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_TRUE(block->constraint_items_parsed);
  EXPECT_EQ(
      KindsOf(block->constraint_items),
      (std::vector<ConstraintItemKind>{
          ConstraintItemKind::kSolveBefore, ConstraintItemKind::kExpression,
          ConstraintItemKind::kUnique, ConstraintItemKind::kExpression,
          ConstraintItemKind::kExpression, ConstraintItemKind::kDisableSoft}));
  EXPECT_EQ(block->constraint_items[1]->dist.size(), 2U);
  EXPECT_EQ(block->constraint_items[2]->exprs.size(), 2U);
  EXPECT_TRUE(block->constraint_items[4]->soft);
}

TEST(ConstraintItems, ASolveBeforeKeepsBothLists) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { solve a, b before x; }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  EXPECT_EQ(block->constraint_items[0]->exprs.size(), 2U);
  EXPECT_EQ(block->constraint_items[0]->after.size(), 1U);
}

TEST(ConstraintItems, AnImplicationKeepsTheSetItGoverns) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { a > 0 -> { b == 1; soft x == 2; } }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  const ConstraintItem* item = block->constraint_items[0];
  EXPECT_EQ(item->kind, ConstraintItemKind::kImplication);
  ASSERT_EQ(item->body.size(), 2U);
  EXPECT_TRUE(item->body[1]->soft);
}

TEST(ConstraintItems, AnElseBindsToTheClosestIf) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { if (a) if (b) x == 1; else { x == 2; x < 3; } }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  const ConstraintItem* outer = block->constraint_items[0];
  EXPECT_FALSE(outer->has_else);
  ASSERT_EQ(outer->body.size(), 1U);
  const ConstraintItem* inner = outer->body[0];
  EXPECT_EQ(inner->kind, ConstraintItemKind::kIfElse);
  EXPECT_TRUE(inner->has_else);
  EXPECT_EQ(inner->else_body.size(), 2U);
}

TEST(ConstraintItems, AForeachKeepsItsLoopVariables) {
  auto r = Parse(
      "class C;\n"
      "  rand int m[2][3][4];\n"
      "  constraint c { foreach (m[i, , k]) m[i][0][k] < 4; }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  const ConstraintItem* item = block->constraint_items[0];
  EXPECT_EQ(item->kind, ConstraintItemKind::kForeach);
  EXPECT_EQ(item->loop_vars, (std::vector<std::string_view>{"i", "", "k"}));
  EXPECT_EQ(item->body.size(), 1U);
}

}  // namespace
