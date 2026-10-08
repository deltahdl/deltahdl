#include <gtest/gtest.h>

#include <cstddef>
#include <deque>
#include <string_view>
#include <utility>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/vpi_expr_decompile.h"

namespace delta {
namespace {

// §37.59 detail 2: the vpiDecompile text of an expression, read off
// expressions and constraint blocks built by hand, so that each part a run
// rarely writes, and each part that cannot be written, can be named.
class DecompileByHand : public ::testing::Test {
 protected:
  Expr* Make(ExprKind kind, std::string_view text = {}) {
    Expr& expr = exprs_.emplace_back();
    expr.kind = kind;
    expr.text = text;
    return &expr;
  }
  Expr* Name(std::string_view text) {
    return Make(ExprKind::kIdentifier, text);
  }
  // A literal written with no text, which nothing can render.
  Expr* Unrenderable() { return Make(ExprKind::kIntegerLiteral); }
  Expr* Operation(ExprKind kind, TokenKind op, Expr* lhs, Expr* rhs) {
    Expr* expr = Make(kind);
    expr->op = op;
    expr->lhs = lhs;
    expr->rhs = rhs;
    return expr;
  }
  Expr* Ternary(Expr* condition, Expr* first, Expr* second) {
    Expr* expr = Make(ExprKind::kTernary);
    expr->condition = condition;
    expr->true_expr = first;
    expr->false_expr = second;
    return expr;
  }
  Expr* Select(Expr* base, Expr* index, Expr* index_end) {
    Expr* expr = Make(ExprKind::kSelect);
    expr->base = base;
    expr->index = index;
    expr->index_end = index_end;
    return expr;
  }
  Expr* WithElements(ExprKind kind, std::vector<Expr*> elements) {
    Expr* expr = Make(kind);
    expr->elements = std::move(elements);
    return expr;
  }
  Expr* MinTypMax(Expr* min, Expr* typ, Expr* max) {
    Expr* expr = Make(ExprKind::kMinTypMax);
    expr->lhs = min;
    expr->condition = typ;
    expr->rhs = max;
    return expr;
  }
  ConstraintItem* Item(ConstraintItemKind kind, Expr* expr) {
    ConstraintItem& item = items_.emplace_back();
    item.kind = kind;
    item.expr = expr;
    return &item;
  }
  // A randomize() call with `items` as its inline constraint block.
  Expr* Randomize(std::vector<ConstraintItem*> items, bool parsed = true) {
    ClassMember& block = members_.emplace_back();
    block.constraint_items = std::move(items);
    block.constraint_items_parsed = parsed;
    Expr* call = Make(ExprKind::kCall);
    call->lhs = Name("randomize");
    call->inline_constraint = &block;
    return call;
  }

  std::deque<Expr> exprs_;
  std::deque<ConstraintItem> items_;
  std::deque<ClassMember> members_;
};

// An expression one of whose parts cannot be rendered has no decompiled text
// at all, whichever part that is.
TEST_F(DecompileByHand, AnUnrenderablePartLeavesNoText) {
  const std::vector<Expr*> kCases = {
      nullptr,
      Unrenderable(),
      Operation(ExprKind::kUnary, TokenKind::kMinus, Unrenderable(), nullptr),
      Operation(ExprKind::kUnary, TokenKind::kComma, Name("a"), nullptr),
      Operation(ExprKind::kBinary, TokenKind::kPlus, Unrenderable(), Name("b")),
      Operation(ExprKind::kBinary, TokenKind::kPlus, Name("a"), Unrenderable()),
      Operation(ExprKind::kBinary, TokenKind::kComma, Name("a"), Name("b")),
      Ternary(Unrenderable(), Name("a"), Name("b")),
      Ternary(Name("c"), Unrenderable(), Name("b")),
      Ternary(Name("c"), Name("a"), Unrenderable()),
      Operation(ExprKind::kMemberAccess, TokenKind::kDot, Unrenderable(),
                Name("m")),
      Operation(ExprKind::kMemberAccess, TokenKind::kDot, Name("s"),
                Unrenderable()),
      Select(Unrenderable(), Name("i"), nullptr),
      Select(Name("v"), Unrenderable(), nullptr),
      Select(Name("v"), Name("i"), Unrenderable()),
      WithElements(ExprKind::kConcatenation, {Unrenderable()}),
      Operation(ExprKind::kCast, TokenKind::kEof, Name("x"), Unrenderable()),
      Operation(ExprKind::kCast, TokenKind::kEof, Unrenderable(), Name("W")),
      MinTypMax(Unrenderable(), Name("t"), Name("x")),
      MinTypMax(Name("n"), Unrenderable(), Name("x")),
      MinTypMax(Name("n"), Name("t"), Unrenderable()),
  };
  for (std::size_t i = 0; i < kCases.size(); ++i) {
    EXPECT_EQ(VpiExprDecompile(kCases[i]), "") << i;
  }

  Expr* replicate = WithElements(ExprKind::kReplicate, {Name("a")});
  replicate->repeat_count = Unrenderable();
  EXPECT_EQ(VpiExprDecompile(replicate), "");

  Expr* inside = WithElements(ExprKind::kInside, {Name("a")});
  inside->lhs = Unrenderable();
  EXPECT_EQ(VpiExprDecompile(inside), "");
  Expr* inside_set = WithElements(ExprKind::kInside, {Unrenderable()});
  inside_set->lhs = Name("v");
  EXPECT_EQ(VpiExprDecompile(inside_set), "");

  Expr* stream = WithElements(ExprKind::kStreamingConcat, {Name("a")});
  stream->op = TokenKind::kLtLt;
  stream->lhs = Unrenderable();
  EXPECT_EQ(VpiExprDecompile(stream), "");
  Expr* stream_elements =
      WithElements(ExprKind::kStreamingConcat, {Unrenderable()});
  stream_elements->op = TokenKind::kLtLt;
  EXPECT_EQ(VpiExprDecompile(stream_elements), "");

  Expr* call = Make(ExprKind::kCall);
  call->lhs = Unrenderable();
  EXPECT_EQ(VpiExprDecompile(call), "");
  Expr* system_call = Make(ExprKind::kSystemCall);
  system_call->callee = "$display";
  system_call->args = {Unrenderable()};
  EXPECT_EQ(VpiExprDecompile(system_call), "");
  Expr* with_call = Make(ExprKind::kCall);
  with_call->lhs = Name("find");
  with_call->with_expr = Unrenderable();
  EXPECT_EQ(VpiExprDecompile(with_call), "");
}

// The parts a run seldom writes: an argument bound by name, a name under
// $root or a package, a time literal, a cast to a size, the ranges of an
// inside expression's set, a streaming slice size and a with clause written
// without parentheses.
TEST_F(DecompileByHand, PartsARunSeldomWrites) {
  Expr* call = Make(ExprKind::kCall);
  call->lhs = Name("f");
  call->args = {Name("x"), Name("y")};
  call->arg_names = {"a", ""};
  EXPECT_EQ(VpiExprDecompile(call), "f(.a(x), y)");

  Expr* rooted = Name("a");
  rooted->scope_prefix = "$root";
  EXPECT_EQ(VpiExprDecompile(rooted), "$root.a");
  Expr* packaged = Name("b");
  packaged->scope_prefix = "pkg";
  EXPECT_EQ(VpiExprDecompile(packaged), "pkg::b");
  EXPECT_EQ(VpiExprDecompile(Make(ExprKind::kTimeLiteral, "1ns")), "1ns");

  EXPECT_EQ(VpiExprDecompile(Operation(ExprKind::kCast, TokenKind::kEof,
                                       Name("x"), Name("W"))),
            "W'(x)");
  EXPECT_EQ(
      VpiExprDecompile(Operation(ExprKind::kCast, TokenKind::kEof, Name("x"),
                                 Operation(ExprKind::kBinary, TokenKind::kPlus,
                                           Name("a"), Name("b")))),
      "(a + b)'(x)");
  EXPECT_EQ(
      VpiExprDecompile(Operation(
          ExprKind::kCast, TokenKind::kEof, Name("x"),
          Operation(ExprKind::kUnary, TokenKind::kMinus, Name("W"), nullptr))),
      "(- W)'(x)");

  Expr* about = Select(nullptr, Name("c"), Name("t"));
  about->op = TokenKind::kPlusSlashMinus;
  Expr* relative = Select(nullptr, Name("c"), Name("p"));
  relative->op = TokenKind::kPlusPercentMinus;
  Expr* inside = WithElements(ExprKind::kInside, {about, relative});
  inside->lhs = Name("v");
  EXPECT_EQ(VpiExprDecompile(inside), "v inside {[c+/-t], [c+%-p]}");

  Expr* stream = WithElements(ExprKind::kStreamingConcat, {Name("a")});
  stream->op = TokenKind::kLtLt;
  stream->lhs = Make(ExprKind::kIntegerLiteral, "8");
  EXPECT_EQ(VpiExprDecompile(stream), "{<< 8 {a}}");

  Expr* with_call = Make(ExprKind::kCall);
  with_call->lhs = Name("find");
  with_call->with_expr = Name("x");
  EXPECT_EQ(VpiExprDecompile(with_call), "find() with x");
}

// An operator kind whose name is no quoted spelling, as a token's kind that is
// no operator is, writes as nothing in the streaming operator's place.
TEST_F(DecompileByHand, AKindWithNoSpellingWritesNothing) {
  for (TokenKind op : {TokenKind::kApostrophe, TokenKind::kEof}) {
    Expr* stream = WithElements(ExprKind::kStreamingConcat, {Name("a")});
    stream->op = op;
    EXPECT_EQ(VpiExprDecompile(stream), "{{a}}");
  }
}

// §18.7 with §18.5: a randomize() call's inline constraint block is written
// back item by item, each kind of constraint item as the source writes it.
TEST_F(DecompileByHand, AnInlineConstraintBlockIsWrittenBack) {
  ConstraintItem* dist = Item(ConstraintItemKind::kExpression, Name("x"));
  dist->soft = true;
  dist->has_dist = true;
  dist->dist.resize(4);
  dist->dist[0].is_default = true;
  dist->dist[0].weight = Make(ExprKind::kIntegerLiteral, "1");
  dist->dist[0].per_element = true;
  dist->dist[1].is_range = true;
  dist->dist[1].lo = Name("c");
  dist->dist[1].tolerance = Name("t");
  dist->dist[1].tolerance_relative = true;
  dist->dist[2].value = Make(ExprKind::kIntegerLiteral, "5");
  dist->dist[3].is_range = true;
  dist->dist[3].lo = Name("d");
  dist->dist[3].tolerance = Name("u");

  ConstraintItem* unique = Item(ConstraintItemKind::kUnique, nullptr);
  unique->exprs = {Name("a"), Name("b")};
  ConstraintItem* disable = Item(ConstraintItemKind::kDisableSoft, Name("a"));
  ConstraintItem* solve = Item(ConstraintItemKind::kSolveBefore, nullptr);
  solve->exprs = {Name("a")};
  solve->after = {Name("b")};
  ConstraintItem* implication =
      Item(ConstraintItemKind::kImplication, Name("c"));
  implication->body = {Item(ConstraintItemKind::kExpression, Name("a"))};
  ConstraintItem* if_else = Item(ConstraintItemKind::kIfElse, Name("c"));
  if_else->body = {Item(ConstraintItemKind::kExpression, Name("a"))};
  if_else->has_else = true;
  if_else->else_body = {Item(ConstraintItemKind::kExpression, Name("b"))};
  ConstraintItem* foreach_item =
      Item(ConstraintItemKind::kForeach, Name("arr"));
  foreach_item->loop_vars = {"i", "j"};
  foreach_item->body = {Item(ConstraintItemKind::kExpression, Name("a"))};

  Expr* call = Randomize(
      {dist, unique, disable, solve, implication, if_else, foreach_item});
  call->with_restrict_ids = {"a", "b"};
  call->with_has_parens = true;
  EXPECT_EQ(VpiExprDecompile(call),
            "randomize() with (a, b) {soft x dist {default := 1, [c+%-t], "
            "5, [d+/-u]}; unique {a, b}; disable soft a; solve a before b; "
            "c -> {a;} if (c) {a;} else {b;} foreach (arr[i, j]) {a;}}");
}

// An inline constraint block one of whose items cannot be written back, or
// that was never parsed into items, leaves the call no decompiled text.
TEST_F(DecompileByHand, AnUnwritableConstraintItemLeavesNoText) {
  auto unrenderable_dist = [&](int which) {
    ConstraintItem* item = Item(ConstraintItemKind::kExpression, Name("x"));
    item->has_dist = true;
    item->dist.resize(1);
    ConstraintDistItem& dist_item = item->dist[0];
    dist_item.value = Name("v");
    if (which == 0) dist_item.value = Unrenderable();
    if (which == 1 || which == 2) {
      dist_item.is_range = true;
      dist_item.lo = which == 1 ? Unrenderable() : Name("lo");
      dist_item.hi = which == 2 ? Unrenderable() : Name("hi");
    }
    if (which == 3) dist_item.weight = Unrenderable();
    return item;
  };
  ConstraintItem* unique = Item(ConstraintItemKind::kUnique, nullptr);
  unique->exprs = {Unrenderable()};
  ConstraintItem* solve_before =
      Item(ConstraintItemKind::kSolveBefore, nullptr);
  solve_before->exprs = {Unrenderable()};
  solve_before->after = {Name("b")};
  ConstraintItem* solve_after = Item(ConstraintItemKind::kSolveBefore, nullptr);
  solve_after->exprs = {Name("a")};
  solve_after->after = {Unrenderable()};
  ConstraintItem* bad_body = Item(ConstraintItemKind::kImplication, Name("c"));
  bad_body->body = {Item(ConstraintItemKind::kExpression, Unrenderable())};
  ConstraintItem* bad_else = Item(ConstraintItemKind::kIfElse, Name("c"));
  bad_else->body = {Item(ConstraintItemKind::kExpression, Name("a"))};
  bad_else->has_else = true;
  bad_else->else_body = {Item(ConstraintItemKind::kExpression, Unrenderable())};

  const std::vector<ConstraintItem*> kItems = {
      nullptr,
      Item(ConstraintItemKind::kExpression, Unrenderable()),
      unrenderable_dist(0),
      unrenderable_dist(1),
      unrenderable_dist(2),
      unrenderable_dist(3),
      unique,
      Item(ConstraintItemKind::kDisableSoft, Unrenderable()),
      solve_before,
      solve_after,
      Item(ConstraintItemKind::kImplication, Unrenderable()),
      bad_body,
      bad_else,
      Item(ConstraintItemKind::kForeach, Unrenderable()),
  };
  for (std::size_t i = 0; i < kItems.size(); ++i) {
    EXPECT_EQ(VpiExprDecompile(Randomize({kItems[i]})), "") << i;
  }
  EXPECT_EQ(VpiExprDecompile(Randomize({}, /*parsed=*/false)), "");
}

}  // namespace
}  // namespace delta
