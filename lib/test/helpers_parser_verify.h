#pragma once

#include <gtest/gtest.h>

#include <initializer_list>
#include <utility>

#include "parser/ast.h"

using namespace delta;

// Verify clocking signal directions and names.
inline void VerifyClockingSignalDirections(
    ModuleItem* item,
    std::initializer_list<std::pair<Direction, const char*>> expected) {
  ASSERT_EQ(item->clocking_signals.size(), expected.size());
  size_t i = 0;
  for (auto& [dir, name] : expected) {
    EXPECT_EQ(item->clocking_signals[i].direction, dir) << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].name, name) << "signal " << i;
    ++i;
  }
}

// Verify full-path src_ports and dst_ports by name.
inline void VerifyFullPathPorts(SpecifyItem* si,
                                std::initializer_list<const char*> src,
                                std::initializer_list<const char*> dst) {
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), src.size());
  size_t i = 0;
  for (auto* name : src) {
    EXPECT_EQ(si->path.src_ports[i].name, name) << "src port " << i;
    ++i;
  }
  ASSERT_EQ(si->path.dst_ports.size(), dst.size());
  i = 0;
  for (auto* name : dst) {
    EXPECT_EQ(si->path.dst_ports[i].name, name) << "dst port " << i;
    ++i;
  }
}

// Verify ternary expression: condition, true_expr, false_expr all kIdentifier.
inline void VerifyTernaryFieldsAllIdentifier(Expr* expr) {
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kTernary);
  ASSERT_NE(expr->condition, nullptr);
  EXPECT_EQ(expr->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(expr->true_expr, nullptr);
  EXPECT_EQ(expr->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(expr->false_expr, nullptr);
  EXPECT_EQ(expr->false_expr->kind, ExprKind::kIdentifier);
}

// Verify func_args directions.
inline void VerifyFuncArgDirections(ModuleItem* item,
                                    std::initializer_list<Direction> expected) {
  ASSERT_EQ(item->func_args.size(), expected.size());
  size_t i = 0;
  for (auto dir : expected) {
    EXPECT_EQ(item->func_args[i].direction, dir) << "arg " << i;
    ++i;
  }
}

// Verify forever-loop body has jump statement of given kind.
inline void VerifyForeverLoopJump(Stmt* body, StmtKind expected) {
  ASSERT_NE(body, nullptr);
  auto* forever_stmt = body->stmts[0];
  ASSERT_NE(forever_stmt, nullptr);
  EXPECT_EQ(forever_stmt->kind, StmtKind::kForever);
  auto* loop_body = forever_stmt->body;
  ASSERT_NE(loop_body, nullptr);
  EXPECT_EQ(loop_body->stmts[0]->kind, expected);
}

// Template AST navigation: first statement inside the first initial block.
template <typename T>
inline Stmt* FirstInitialStmtT(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// Template AST navigation: body of the first initial block.
template <typename T>
inline Stmt* InitialBodyT(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) return item->body;
  }
  return nullptr;
}
