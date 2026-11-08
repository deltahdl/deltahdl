#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <iterator>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct PatternParam {
  const DataType* type;
  const Expr* value;
};

struct PatternNames {
  std::unordered_map<std::string_view, const DataType*> vars;
  std::unordered_map<std::string_view, PatternParam> params;

  void AddVar(std::string_view name, const DataType& type, bool unpacked) {
    vars[name] = unpacked ? nullptr : &type;
    params.erase(name);
  }
  void AddParam(std::string_view name, const DataType& type,
                const Expr* value) {
    params[name] = PatternParam{&type, value};
    vars.erase(name);
  }
};

struct PatternCtx {
  const TypedefMap& typedefs;
  DiagEngine& diag;
};

struct MatchedType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  const DataType* decl = nullptr;
};

MatchedType MatchedTypeOf(const DataType& type, const PatternCtx& ctx) {
  const DataType* end = TypeAtChainEnd(type, ctx.typedefs);
  if (end == nullptr) return {};
  return {end->kind, end};
}

MatchedType MatchedTypeOfMember(const StructMember& m, const PatternCtx& ctx) {
  if (m.nested_type != nullptr) return MatchedTypeOf(*m.nested_type, ctx);
  if (m.type_kind != DataTypeKind::kNamed) return {m.type_kind, nullptr};
  const DataType* named = MemberNamedType(m, ctx.typedefs);
  return named == nullptr ? MatchedType{} : MatchedTypeOf(*named, ctx);
}

const StructMember* FindMember(const DataType& aggregate,
                               std::string_view name) {
  for (const auto& m : aggregate.struct_members) {
    if (m.name == name) return &m;
  }
  return nullptr;
}

MatchedType MatchedTypeOfValue(const Expr* e, const PatternNames& names,
                               const PatternCtx& ctx) {
  if (e->kind == ExprKind::kIdentifier) {
    auto it = names.vars.find(e->text);
    if (it == names.vars.end() || it->second == nullptr) return {};
    return MatchedTypeOf(*it->second, ctx);
  }
  if (e->kind != ExprKind::kMemberAccess) return {};
  MatchedType base = MatchedTypeOfValue(e->lhs, names, ctx);
  if (base.decl == nullptr || e->rhs == nullptr) return {};
  const StructMember* m = FindMember(*base.decl, e->rhs->text);
  return m == nullptr ? MatchedType{} : MatchedTypeOfMember(*m, ctx);
}

void CheckPatternAgainst(const Expr* p, const MatchedType& target,
                         const PatternCtx& ctx);

void CheckTaggedPattern(const Expr* p, const MatchedType& target,
                        const PatternCtx& ctx) {
  if (target.kind == DataTypeKind::kImplicit) return;
  if (target.kind != DataTypeKind::kUnion || !target.decl->is_tagged) {
    ctx.diag.Error(p->range.start,
                   "tagged pattern is matched against a value that is not a "
                   "tagged union",
                   Subclause("12.6"));
    return;
  }
  std::string_view name = p->rhs->text;
  const StructMember* member = FindMember(*target.decl, name);
  if (member == nullptr) {
    ctx.diag.Error(p->range.start,
                   std::format("tagged pattern names '{}', which is not a "
                               "member of the tagged union",
                               name),
                   Subclause("12.6"));
  } else if (member->type_kind == DataTypeKind::kVoid) {
    if (p->lhs != nullptr) {
      ctx.diag.Error(p->range.start,
                     std::format("tagged pattern for void member '{}' has a "
                                 "member pattern",
                                 name),
                     Subclause("12.6"));
    }
  } else if (p->lhs != nullptr) {
    CheckPatternAgainst(p->lhs, MatchedTypeOfMember(*member, ctx), ctx);
  }
}

void CheckStructurePattern(const Expr* p, const MatchedType& target,
                           const PatternCtx& ctx) {
  if (target.kind == DataTypeKind::kImplicit) return;
  if (target.kind != DataTypeKind::kStruct) {
    ctx.diag.Error(p->range.start,
                   "structure pattern is matched against a value that is not "
                   "a structure",
                   Subclause("12.6"));
    return;
  }
  const auto& members = target.decl->struct_members;
  if (!p->pattern_keys.empty()) {
    for (size_t i = 0; i < p->pattern_keys.size(); ++i) {
      const Expr* key = p->pattern_keys[i];
      const StructMember* m = FindMember(*target.decl, key->text);
      if (m == nullptr) {
        ctx.diag.Error(key->range.start,
                       std::format("structure pattern names '{}', which is "
                                   "not a member of the structure",
                                   key->text),
                       Subclause("12.6"));
        continue;
      }
      CheckPatternAgainst(p->elements[i], MatchedTypeOfMember(*m, ctx), ctx);
    }
    return;
  }
  if (p->elements.size() != members.size()) {
    ctx.diag.Error(p->range.start,
                   std::format("structure pattern lists {} element(s) but the "
                               "structure has {} member(s)",
                               p->elements.size(), members.size()),
                   Subclause("12.6"));
  }
  for (size_t i = 0; i < std::min(p->elements.size(), members.size()); ++i) {
    CheckPatternAgainst(p->elements[i], MatchedTypeOfMember(members[i], ctx),
                        ctx);
  }
}

void CheckPatternAgainst(const Expr* p, const MatchedType& target,
                         const PatternCtx& ctx) {
  if (p->kind == ExprKind::kTagged) {
    CheckTaggedPattern(p, target, ctx);
  } else if (p->kind == ExprKind::kAssignmentPattern) {
    CheckStructurePattern(p, target, ctx);
  }
}

enum class ConstantKind : uint8_t { kUnknown, kIntegral, kReal, kString };

ConstantKind KindOfConstant(const Expr* e, const PatternNames& names,
                            const PatternCtx& ctx, int depth);

ConstantKind KindOfType(DataTypeKind k) {
  if (IsRealType(k)) return ConstantKind::kReal;
  if (k == DataTypeKind::kString) return ConstantKind::kString;
  return IsIntegralType(k) ? ConstantKind::kIntegral : ConstantKind::kUnknown;
}

ConstantKind KindOfParam(std::string_view name, const PatternNames& names,
                         const PatternCtx& ctx, int depth) {
  auto it = names.params.find(name);
  if (it == names.params.end() || depth == 0) return ConstantKind::kUnknown;
  const DataType& type = *it->second.type;
  if (type.kind != DataTypeKind::kImplicit) {
    return KindOfType(ResolvedTypeKind(type, ctx.typedefs));
  }
  if (type.packed_dim_left != nullptr) return ConstantKind::kIntegral;
  const Expr* value = it->second.value;
  return value == nullptr ? ConstantKind::kUnknown
                          : KindOfConstant(value, names, ctx, depth - 1);
}

ConstantKind KindOfArithmetic(const Expr* e, const PatternNames& names,
                              const PatternCtx& ctx, int depth) {
  static constexpr TokenKind kArithmetic[] = {
      TokenKind::kPlus, TokenKind::kMinus, TokenKind::kStar, TokenKind::kSlash,
      TokenKind::kPower};
  if (std::ranges::find(kArithmetic, e->op) == std::end(kArithmetic)) {
    return ConstantKind::kUnknown;
  }
  ConstantKind l = KindOfConstant(e->lhs, names, ctx, depth);
  ConstantKind r = KindOfConstant(e->rhs, names, ctx, depth);
  if (l == ConstantKind::kReal || r == ConstantKind::kReal) {
    return ConstantKind::kReal;
  }
  return l == ConstantKind::kIntegral && r == ConstantKind::kIntegral
             ? ConstantKind::kIntegral
             : ConstantKind::kUnknown;
}

ConstantKind KindOfConstant(const Expr* e, const PatternNames& names,
                            const PatternCtx& ctx, int depth) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kStringLiteral:
      return ConstantKind::kIntegral;
    case ExprKind::kRealLiteral:
      return ConstantKind::kReal;
    case ExprKind::kIdentifier:
      return e->is_pattern_binding ? ConstantKind::kUnknown
                                   : KindOfParam(e->text, names, ctx, depth);
    case ExprKind::kBinary:
      return KindOfArithmetic(e, names, ctx, depth);
    default:
      return ConstantKind::kUnknown;
  }
}

constexpr int kParamDepth = 8;

template <typename Visit>
void ForEachConstantPattern(const Expr* p, Visit visit) {
  if (p == nullptr) return;
  if (p->kind == ExprKind::kTagged) {
    ForEachConstantPattern(p->lhs, visit);
  } else if (p->kind == ExprKind::kAssignmentPattern) {
    for (const Expr* e : p->elements) ForEachConstantPattern(e, visit);
  } else if (p->kind != ExprKind::kIdentifier ||
             (!p->is_pattern_binding && p->text != ".*")) {
    visit(p);
  }
}

const Expr* WithoutFilter(const Expr* pat) {
  if (pat->kind == ExprKind::kBinary && pat->op == TokenKind::kAmpAmpAmp) {
    return pat->lhs;
  }
  return pat;
}

void CheckPatternBindingsUnique(const Expr* pat, DiagEngine& diag) {
  std::unordered_set<std::string_view> seen;
  ForEachPatternBinding(pat, [&](const Expr* binding) {
    if (!seen.insert(binding->text).second) {
      diag.Error(
          binding->range.start,
          std::format("pattern identifier '{}' is used more than once in "
                      "a single pattern",
                      binding->text),
          Subclause("12.6"));
    }
  });
}

void CheckStringValueAgainstConstant(const Expr* p, const Expr* value,
                                     const PatternNames& names,
                                     const PatternCtx& ctx) {
  if (MatchedTypeOfValue(value, names, ctx).kind == DataTypeKind::kString &&
      KindOfConstant(p, names, ctx, kParamDepth) == ConstantKind::kIntegral) {
    ctx.diag.Error(p->range.start,
                   "a string value is matched with an integral constant "
                   "expression pattern",
                   Subclause("12.6"));
  }
}

void CheckPattern(const Expr* pat, const Expr* value, const PatternNames& names,
                  const PatternCtx& ctx) {
  CheckPatternBindingsUnique(pat, ctx.diag);
  const Expr* p = WithoutFilter(pat);
  CheckStringValueAgainstConstant(p, value, names, ctx);
  ForEachConstantPattern(p, [&](const Expr* leaf) {
    ConstantKind k = KindOfConstant(leaf, names, ctx, kParamDepth);
    if (k == ConstantKind::kReal || k == ConstantKind::kString) {
      ctx.diag.Error(leaf->range.start,
                     "only an integral expression can serve as a constant "
                     "expression pattern",
                     Subclause("12.6"));
    } else if (NamesAVariable(leaf, names.vars)) {
      ctx.diag.Error(leaf->range.start,
                     "constant expression pattern is not a constant "
                     "expression",
                     Subclause("12.6"));
    }
  });
  CheckPatternAgainst(p, MatchedTypeOfValue(value, names, ctx), ctx);
}

bool IsRealValue(const Expr* value, const PatternNames& names,
                 const PatternCtx& ctx) {
  return IsRealType(MatchedTypeOfValue(value, names, ctx).kind);
}

bool IsIntegralConstantPattern(const Expr* pat, const PatternNames& names,
                               const PatternCtx& ctx) {
  return KindOfConstant(WithoutFilter(pat), names, ctx, kParamDepth) ==
         ConstantKind::kIntegral;
}

void CheckCaseMatches(const Stmt* s, const PatternNames& names,
                      const PatternCtx& ctx) {
  bool real = IsRealValue(s->condition, names, ctx);
  for (const auto& ci : s->case_items) {
    if (ci.is_default) continue;
    bool reported = false;
    for (const auto* pat : ci.patterns) {
      CheckPattern(pat, s->condition, names, ctx);
      if (real && !reported && IsIntegralConstantPattern(pat, names, ctx)) {
        ctx.diag.Error(s->condition->range.start,
                       "pattern-matching case selector type differs from the "
                       "type of its integral pattern",
                       Subclause("12.6.1"));
        reported = true;
      }
    }
  }
}

void CheckIfPredicate(const Expr* pred, const PatternNames& names,
                      const PatternCtx& ctx) {
  if (pred->kind != ExprKind::kBinary) return;
  if (pred->op == TokenKind::kAmpAmpAmp) {
    CheckIfPredicate(pred->lhs, names, ctx);
    CheckIfPredicate(pred->rhs, names, ctx);
  } else if (pred->op == TokenKind::kKwMatches &&
             IsRealValue(pred->lhs, names, ctx) &&
             IsIntegralConstantPattern(pred->rhs, names, ctx)) {
    ctx.diag.Error(pred->range.start,
                   "pattern-matching if predicate value type differs from "
                   "the type of its integral pattern",
                   Subclause("12.6.2"));
  }
}

void CheckMatchesOperators(const Expr* e, const PatternNames& names,
                           const PatternCtx& ctx) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kBinary && e->op == TokenKind::kKwMatches) {
    CheckPattern(e->rhs, e->lhs, names, ctx);
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckMatchesOperators(child, names, ctx); });
}

void CheckPatternsInStmt(const Stmt* s, const PatternNames& names,
                         const PatternCtx& ctx);

void CheckPatternsInBlockStmts(const std::vector<Stmt*>& subs,
                               PatternNames& names, const PatternCtx& ctx) {
  for (const Stmt* sub : subs) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl) {
      names.AddVar(sub->var_name, sub->var_decl_type,
                   !sub->var_unpacked_dims.empty());
    }
    CheckPatternsInStmt(sub, names, ctx);
  }
}

void CheckPatternsInStmt(const Stmt* s, const PatternNames& names,
                         const PatternCtx& ctx) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kCase && s->case_matches) {
    CheckCaseMatches(s, names, ctx);
  } else if (s->kind == StmtKind::kIf && s->condition != nullptr) {
    CheckIfPredicate(s->condition, names, ctx);
  }
  ForEachChildExpr(
      s, [&](const Expr* e) { CheckMatchesOperators(e, names, ctx); });
  if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) {
    PatternNames inner = names;
    CheckPatternsInBlockStmts(s->stmts, inner, ctx);
    CheckPatternsInBlockStmts(s->fork_stmts, inner, ctx);
    return;
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckPatternsInStmt(sub, names, ctx); });
}

void CheckPatternsInSubroutine(const ModuleItem* item,
                               const PatternNames& names,
                               const PatternCtx& ctx) {
  PatternNames inner = names;
  for (const auto& arg : item->func_args) {
    inner.AddVar(arg.name, arg.data_type, !arg.unpacked_dims.empty());
  }
  CheckPatternsInBlockStmts(item->func_body_stmts, inner, ctx);
}

const TypedefMap& NoTypedefs() {
  static const TypedefMap kNone;
  return kNone;
}

void CheckPatternsInClassBody(const ClassDecl* cls, const PatternNames& names,
                              const PatternCtx& outer) {
  PatternCtx ctx{NoTypedefs(), outer.diag};
  PatternNames inner = names;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    if (m->is_param) {
      inner.AddParam(m->name, m->data_type, m->init_expr);
    } else {
      inner.AddVar(m->name, m->data_type, !m->unpacked_dims.empty());
    }
  }
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      CheckPatternsInSubroutine(m->method, inner, ctx);
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      CheckPatternsInClassBody(m->nested_class, inner, ctx);
    }
  }
}

void AddItemName(const ModuleItem* item, PatternNames& names) {
  if (item->kind == ModuleItemKind::kVarDecl ||
      item->kind == ModuleItemKind::kNetDecl) {
    names.AddVar(item->name, item->data_type, !item->unpacked_dims.empty());
  } else if (item->kind == ModuleItemKind::kParamDecl) {
    names.AddParam(item->name, item->data_type, item->init_expr);
  }
}

void AddItemNames(const std::vector<ModuleItem*>& items, PatternNames& names) {
  for (const auto* item : items) {
    if (item != nullptr) AddItemName(item, names);
  }
}

void CheckPatternsInItem(const ModuleItem* item, const PatternNames& names,
                         const PatternCtx& ctx) {
  if (item->kind == ModuleItemKind::kClassDecl) {
    CheckPatternsInClassBody(item->class_decl, names, ctx);
  } else if (IsProceduralItemKind(item->kind)) {
    CheckPatternsInStmt(item->body, names, ctx);
  } else if (item->kind == ModuleItemKind::kFunctionDecl ||
             item->kind == ModuleItemKind::kTaskDecl) {
    CheckPatternsInSubroutine(
        item, names,
        item->method_class.empty() ? ctx : PatternCtx{NoTypedefs(), ctx.diag});
  }
}

void CheckPatternsInItems(const std::vector<ModuleItem*>& items,
                          const PatternNames& names, const PatternCtx& ctx) {
  for (const auto* item : items) {
    if (item != nullptr) CheckPatternsInItem(item, names, ctx);
  }
}

}  // namespace

void Elaborator::ValidatePatterns(const ModuleDecl* decl) {
  PatternNames names;
  for (const auto& port : decl->ports) {
    names.AddVar(port.name, port.data_type, !port.unpacked_dims.empty());
  }
  for (size_t i = 0; i < decl->params.size() && i < decl->param_types.size();
       ++i) {
    names.AddParam(decl->params[i].first, decl->param_types[i],
                   decl->params[i].second);
  }
  AddItemNames(decl->items, names);
  CheckPatternsInItems(decl->items, names, PatternCtx{typedefs_, diag_});
}

void Elaborator::CheckPatternsIn(const std::vector<ModuleItem*>& items) {
  PatternNames names;
  AddItemNames(items, names);
  CheckPatternsInItems(items, names, PatternCtx{typedefs_, diag_});
}

void Elaborator::CheckPatternsInClass(const ClassDecl* cls) {
  CheckPatternsInClassBody(cls, PatternNames{}, PatternCtx{typedefs_, diag_});
}

}  // namespace delta
