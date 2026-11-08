#pragma once

#include <cstddef>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "parser/ast_type.h"

namespace delta {

struct EventExpr;
struct Expr;
struct ModuleDecl;
struct ModuleItem;
struct PropertyExprNode;
struct SeqLinearBody;
struct SeqMatchAssign;
struct Stmt;

using NamedDecls = std::unordered_map<std::string_view, const ModuleItem*>;

void ForEachProceduralStmt(const ModuleItem* item,
                           const std::function<void(const Stmt*)>& fn);

void ForEachConcurrentAssertion(const ModuleDecl* decl,
                                const std::function<void(const Stmt*)>& fn);

NamedDecls NamedDeclsByName(const ModuleDecl* decl, bool with_properties);

void ForEachSubExpr(const Expr* e, const std::function<void(const Expr*)>& fn);

bool AnySubExpr(const Expr* e, const std::function<bool(const Expr*)>& pred);

void ForEachBody(const SeqLinearBody& body,
                 const std::function<void(const SeqLinearBody&)>& fn);

void ForEachBodyExpr(const SeqLinearBody& body,
                     const std::function<void(const Expr*)>& fn);

void ForEachTreeNode(const PropertyExprNode* node,
                     const std::function<void(const PropertyExprNode&)>& fn);

void ForEachTreeExpr(const PropertyExprNode* node,
                     const std::function<void(const Expr*)>& fn);

const ModuleItem* InstantiatedDecl(const Expr* e, const NamedDecls& decls);

bool IsNameRef(const Expr* e, std::string_view name);

bool IsLocalRef(const Expr* e,
                const std::unordered_set<std::string_view>& locals);

bool RepeatedFromZero(const SeqLinearBody& body, size_t i);

std::string_view SequenceMethodOf(const Expr* e);

std::vector<Direction> LocalFormalDirections(const ModuleItem* seq);

bool EventsMention(const std::vector<EventExpr>& events,
                   const std::unordered_set<std::string_view>& names);

bool IsOutward(Direction dir);

bool ItemsAssign(const std::vector<SeqMatchAssign>& items,
                 std::string_view name);

bool BodyAssigns(const SeqLinearBody& body, std::string_view name);

struct FormalReferences {
  int all = 0;
  int permitted = 0;
};

void CountFormalInExpr(const Expr* e, std::string_view name,
                       FormalReferences& refs);

void CountFormalInBody(const SeqLinearBody& body, std::string_view name,
                       FormalReferences& refs);

void CountFormalInTree(const PropertyExprNode* node, std::string_view name,
                       FormalReferences& refs);

}  // namespace delta
