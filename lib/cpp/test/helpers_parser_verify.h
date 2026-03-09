#pragma once

#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "fixture_parser.h"
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
inline ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// Template overload: find item by kind from a parse result.
template <typename T, typename = decltype(std::declval<T>().cu)>
inline ModuleItem* FindItemByKind(T& r, ModuleItemKind kind) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  return FindItemByKind(r.cu->modules[0]->items, kind);
}

// Count module items of a given kind.
inline size_t CountItemsByKind(const std::vector<ModuleItem*>& items,
                               ModuleItemKind kind) {
  size_t count = 0;
  for (auto* item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

// Check if any module item of a given kind exists.
inline bool HasItemOfKind(const std::vector<ModuleItem*>& items,
                          ModuleItemKind kind) {
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

// Get the very first module item (regardless of kind).
template <typename T>
inline ModuleItem* FirstItem(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
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
    if (item->kind == ModuleItemKind::kContAssign) return item->assign_rhs;
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
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) return item;
  }
  return nullptr;
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

// Find the specify block from a vector of module items.
inline ModuleItem* FindSpecifyBlock(std::vector<ModuleItem*>& items) {
  return FindItemByKind(items, ModuleItemKind::kSpecifyBlock);
}
inline ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  return FindItemByKind(items, ModuleItemKind::kSpecifyBlock);
}

// Get the sole specify item from a specify block.
inline SpecifyItem* GetSoleSpecifyItem(ModuleItem* spec_block) {
  EXPECT_EQ(spec_block->specify_items.size(), 1u);
  if (spec_block->specify_items.empty()) return nullptr;
  return spec_block->specify_items[0];
}

// Get the sole path/specify item from a parse result.
template <typename T>
inline SpecifyItem* GetSolePathItem(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  return spec->specify_items[0];
}

// Get the sole timing check declaration from a parse result.
template <typename T>
inline TimingCheckDecl* GetSoleTimingCheck(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  if (spec->specify_items[0]->kind != SpecifyItemKind::kTimingCheck)
    return nullptr;
  return &spec->specify_items[0]->timing_check;
}

// Result of parsing a module with a single specify item.
struct SpecifyParseResult {
  ParseResult pr;
  ModuleItem* spec_block = nullptr;
  SpecifyItem* sole_item = nullptr;
};

inline SpecifyParseResult ParseSpecifySingle(const std::string& src) {
  SpecifyParseResult result;
  result.pr = Parse(src);
  if (result.pr.cu == nullptr) return result;
  result.spec_block = FindSpecifyBlock(result.pr.cu->modules[0]->items);
  if (result.spec_block != nullptr) {
    result.sole_item = GetSoleSpecifyItem(result.spec_block);
  }
  return result;
}

// Collect all items of a given kind.
inline std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

// Find all UDP instantiations.
inline std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

// Find all continuous assignments.
inline std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

// Find the Nth clocking block in the first module.
template <typename T>
inline ModuleItem* FindClockingBlockByIndex(T& r, size_t idx = 0) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (count == idx) return item;
    ++count;
  }
  return nullptr;
}

// Validates parse result and retrieves a clocking block via output param.
template <typename T>
inline void GetClockingBlockChecked(T& r, ModuleItem*& out, size_t idx = 0) {
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  out = FindClockingBlockByIndex(r, idx);
  ASSERT_NE(out, nullptr);
}

// Verify always block has var decl as first statement.
inline void VerifyAlwaysVarDecl(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
}

// Verify always block first statement is nested if-else.
inline void VerifyAlwaysNestedIfElse(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

// Return all statements from the first initial block.
template <typename T>
inline std::vector<Stmt*> AllInitialStmts(T& r) {
  if (!r.cu || r.cu->modules.empty()) return {};
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (!item->body) return {};
    if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
    return {item->body};
  }
  return {};
}

// A group of four statements from an initial block.
struct FourStmts {
  Stmt* s0 = nullptr;
  Stmt* s1 = nullptr;
  Stmt* s2 = nullptr;
  Stmt* s3 = nullptr;
};

// Get the first 4 statements from the first initial block.
template <typename T>
inline FourStmts Get4InitialStmts(T& r) {
  FourStmts fs;
  fs.s0 = NthInitialStmt(r, 0);
  fs.s1 = NthInitialStmt(r, 1);
  fs.s2 = NthInitialStmt(r, 2);
  fs.s3 = NthInitialStmt(r, 3);
  EXPECT_NE(fs.s0, nullptr);
  EXPECT_NE(fs.s1, nullptr);
  EXPECT_NE(fs.s2, nullptr);
  EXPECT_NE(fs.s3, nullptr);
  return fs;
}

// Verify a 2-port module has expected names and directions.
inline void VerifyTwoPortModule(ParseResult& r, const char* n0, Direction d0,
                                const char* n1, Direction d1) {
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, n0);
  EXPECT_EQ(mod->ports[0].direction, d0);
  EXPECT_EQ(mod->ports[1].name, n1);
  EXPECT_EQ(mod->ports[1].direction, d1);
}

// --- Aliases for alternative naming conventions ---

inline ModuleItem* FindItem(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind) {
  return FindItemByKind(items, kind);
}

inline bool HasItemKind(const std::vector<ModuleItem*>& items,
                        ModuleItemKind kind) {
  return HasItemOfKind(items, kind);
}

template <typename T>
inline Stmt* FirstInitialBody(T& r) {
  return InitialBody(r);
}

template <typename T>
inline ModuleItem* FirstAlwaysComb(T& r) {
  return FirstAlwaysCombItem(r);
}

template <typename T>
inline Stmt* FirstAlwaysCombStmt(T& r) {
  auto* item = FirstAlwaysCombItem(r);
  return item ? item->body : nullptr;
}

inline bool ParseOk6(const std::string& src) { return ParseOk(src); }

template <typename T>
inline ModuleItem* FirstContAssign(T& r) {
  return FirstItem(r, ModuleItemKind::kContAssign);
}

template <typename T>
inline Expr* FirstContAssignRHS(T& r) {
  return FirstAssignRhs(r);
}

template <typename T>
inline ModuleItem* FirstLetDecl(T& r) {
  return FirstItem(r, ModuleItemKind::kLetDecl);
}

template <typename T>
inline ModuleItem* FirstFuncOrTask(T& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl)
      return item;
  }
  return nullptr;
}

template <typename T>
inline ModuleItem* NthAlwaysItem(T& r, size_t n) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

template <typename T>
inline ModuleItem* NthAlwaysComb(T& r, size_t n) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

inline ModuleItem* FindFunctionByName(const std::vector<ModuleItem*>& items,
                                      std::string_view name) {
  return FindFunc(items, name);
}

// Find the first method member in a class declaration.
inline ClassMember* FindMethodMember(ClassDecl* cls) {
  if (!cls) return nullptr;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method) return m;
  }
  return nullptr;
}

inline ModuleItem* FindMethodMember(const std::vector<ModuleItem*>& items,
                                    std::string_view name) {
  for (auto* item : items) {
    if ((item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl) &&
        item->name == name)
      return item;
  }
  return nullptr;
}

template <typename T>
inline ModuleItem* FindFunc(T& r, std::string_view name) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  return FindMethodMember(r.cu->modules[0]->items, name);
}

inline ModuleItem* FindClassDeclItem(const std::vector<ModuleItem*>& items,
                                     std::string_view name) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->name == name)
      return item;
  }
  return nullptr;
}

inline ModuleItem* FindClassDeclItem(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl) return item;
  }
  return nullptr;
}

inline Stmt* FindStmtByKind(const std::vector<Stmt*>& stmts, StmtKind kind) {
  for (auto* s : stmts) {
    if (s->kind == kind) return s;
  }
  return nullptr;
}

inline bool HasItemKindNamed(const std::vector<ModuleItem*>& items,
                             ModuleItemKind kind, std::string_view name) {
  for (auto* item : items) {
    if (item->kind == kind && item->name == name) return true;
  }
  return false;
}

inline bool HasAttrNamed(ModuleItem* item, std::string_view name) {
  for (auto& attr : item->attrs) {
    if (attr.name == name) return true;
  }
  return false;
}

inline bool HasAttrNamed(const std::vector<ModuleItem*>& items,
                         std::string_view name) {
  for (auto* item : items) {
    if (HasAttrNamed(item, name)) return true;
  }
  return false;
}

inline bool HasAlwaysOfKind(const std::vector<ModuleItem*>& items,
                            AlwaysKind kind) {
  for (auto* item : items) {
    if ((item->kind == ModuleItemKind::kAlwaysBlock ||
         item->kind == ModuleItemKind::kAlwaysCombBlock ||
         item->kind == ModuleItemKind::kAlwaysFFBlock ||
         item->kind == ModuleItemKind::kAlwaysLatchBlock) &&
        item->always_kind == kind)
      return true;
  }
  return false;
}

inline bool HasDefaultCaseItem(const std::vector<CaseItem>& case_items) {
  for (auto& ci : case_items) {
    if (ci.is_default) return true;
  }
  return false;
}
inline bool HasDefaultCaseItem(const Stmt* stmt) {
  if (!stmt) return false;
  return HasDefaultCaseItem(stmt->case_items);
}

template <typename T>
inline Stmt* GetAlwaysStarCaseStmt(T& r) {
  auto* item = FirstAlwaysItem(r);
  if (!item || !item->body) return nullptr;
  if (item->body->kind == StmtKind::kCase) return item->body;
  for (auto* s : item->body->stmts) {
    if (s->kind == StmtKind::kCase) return s;
  }
  return nullptr;
}

template <typename T>
inline Stmt* FindReturnStmt(T& r) {
  auto* func = FirstFunctionDecl(r);
  if (!func) return nullptr;
  auto* ret = FindReturnStmt(func->body);
  if (ret) return ret;
  for (auto* s : func->func_body_stmts) {
    if (s->kind == StmtKind::kReturn) return s;
  }
  return nullptr;
}

template <typename T>
inline ModuleItem* FindClockingBlock(T& r) {
  return FirstItem(r, ModuleItemKind::kClockingBlock);
}

// --- Verify helpers ---

inline void VerifyModportItem(ModportDecl* mp, std::string_view name,
                              Direction dir, std::string_view port_name) {
  EXPECT_EQ(mp->name, name);
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].direction, dir);
  EXPECT_EQ(mp->ports[0].name, port_name);
}

inline void VerifyImportItem(ModuleItem* item, std::string_view pkg,
                             std::string_view name) {
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, pkg);
  EXPECT_EQ(item->import_item.item_name, name);
}

inline void VerifyImportExportPort(const ModportPort& port, bool is_import,
                                   bool is_export, std::string_view name) {
  EXPECT_EQ(port.is_import, is_import);
  EXPECT_EQ(port.is_export, is_export);
  EXPECT_EQ(port.name, name);
}

template <typename T>
inline void VerifyAlwaysMultiAssigns(T& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysCombItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 3u);
}

inline void VerifyPatternKeys(const Expr* rhs,
                              const std::string expected_keys[],
                              size_t count) {
  ASSERT_EQ(rhs->pattern_keys.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(rhs->pattern_keys[i], expected_keys[i]) << "key " << i;
  }
}

template <typename T>
inline void VerifyNestedPatternElements(T& r, size_t count) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->elements.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(stmt->rhs->elements[i]->kind, ExprKind::kAssignmentPattern);
  }
}
