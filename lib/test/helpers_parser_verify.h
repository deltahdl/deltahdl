#pragma once

#include <gtest/gtest.h>

#include <initializer_list>
#include <utility>
#include <vector>

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

// Non-template wrappers for common ParseResult types.
template <typename T>
inline Stmt* FirstInitialStmt(T& r) {
  return FirstInitialStmtT(r);
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

template <typename T>
inline Stmt* InitialBody(T& r) {
  return InitialBodyT(r);
}

// Find the first module item of a given kind.
inline ModuleItem* FindItemByKind(
    const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// Count module items of a given kind.
inline size_t CountItemsByKind(
    const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  size_t count = 0;
  for (auto* item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

// Check if any module item of a given kind exists.
inline bool HasItemOfKind(
    const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  return FindItemByKind(items, kind) != nullptr;
}

// Find the first always block's body item.
template <typename T>
inline ModuleItem* FirstAlwaysItem(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

// Get the first item of a given kind from a module.
template <typename T>
inline ModuleItem* FirstItem(T& r, ModuleItemKind kind) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  return FindItemByKind(r.cu->modules[0]->items, kind);
}

// Find first gate instantiation of a given kind.
inline ModuleItem* FindGateByKind(const std::vector<ModuleItem*>& items,
                                  GateKind kind) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return item;
  }
  return nullptr;
}

// Collect all gate instantiations.
inline std::vector<ModuleItem*> FindAllGates(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> gates;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kGateInst) gates.push_back(item);
  }
  return gates;
}

// Find the first specify block in a module.
template <typename T>
inline ModuleItem* FindSpecifyBlock(T& r) {
  return FirstItem(r, ModuleItemKind::kSpecifyBlock);
}

// Get the Nth statement from the first initial block.
template <typename T>
inline Stmt* NthInitialStmt(T& r, size_t n) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return n < item->body->stmts.size() ? item->body->stmts[n] : nullptr;
    }
    return n == 0 ? item->body : nullptr;
  }
  return nullptr;
}

// Get the RHS expression from the first initial block's first assignment.
template <typename T>
inline Expr* FirstInitialRHS(T& r) {
  auto* stmt = FirstInitialStmt(r);
  return stmt ? stmt->rhs : nullptr;
}

// Get the expression from the first initial block's first statement.
template <typename T>
inline Expr* FirstInitialExpr(T& r) {
  auto* stmt = FirstInitialStmt(r);
  return stmt ? stmt->expr : nullptr;
}

// Get the RHS of the first continuous assignment.
template <typename T>
inline Expr* FirstAssignRhs(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item->rhs;
  }
  return nullptr;
}

// Find the first function declaration.
template <typename T>
inline ModuleItem* FirstFunctionDecl(T& r) {
  return FirstItem(r, ModuleItemKind::kFunctionDecl);
}

// Find the first module instance.
template <typename T>
inline ModuleItem* FirstModuleInst(T& r) {
  return FirstItem(r, ModuleItemKind::kModuleInst);
}

// Find the first always_comb item.
template <typename T>
inline ModuleItem* FirstAlwaysCombItem(T& r) {
  return FirstItem(r, ModuleItemKind::kAlwaysCombBlock);
}

// Find a return statement in a function/task body.
inline Stmt* FindReturnStmt(Stmt* body) {
  if (!body) return nullptr;
  if (body->kind == StmtKind::kReturn) return body;
  for (auto* s : body->stmts) {
    if (s->kind == StmtKind::kReturn) return s;
  }
  return nullptr;
}

// Find the first generate-if item.
template <typename T>
inline ModuleItem* FirstGenerateIf(T& r) {
  return FirstItem(r, ModuleItemKind::kGenerateIf);
}

// Find an item by name.
inline ModuleItem* FindItemByName(const std::vector<ModuleItem*>& items,
                                  std::string_view name) {
  for (auto* item : items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

// Find a function declaration by name.
inline ModuleItem* FindFunc(const std::vector<ModuleItem*>& items,
                            std::string_view name) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == name)
      return item;
  }
  return nullptr;
}

// Find a clocking block by name.
inline ModuleItem* FindClockingBlock(const std::vector<ModuleItem*>& items,
                                     std::string_view name) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock && item->name == name)
      return item;
  }
  return nullptr;
}

// Get the first clocking block.
template <typename T>
inline ModuleItem* GetClockingBlock(T& r) {
  return FirstItem(r, ModuleItemKind::kClockingBlock);
}

// Find a clocking block from a parse result.
template <typename T>
inline ModuleItem* FindClockingBlock(T& r, std::string_view name) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  return FindClockingBlock(r.cu->modules[0]->items, name);
}
