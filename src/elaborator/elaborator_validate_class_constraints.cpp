#include <format>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/class_member_names.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsRealDataType(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

static std::unordered_map<std::string_view, const ClassMember*>
BuildClassPropertyMap(const ClassDecl* cls, const CompilationUnit* unit) {
  std::unordered_map<std::string_view, const ClassMember*> properties;
  for (const ClassDecl* c = cls; c; c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name.empty()) continue;
      properties.emplace(m->name, m);
    }
  }
  return properties;
}

static const DataType* ResolveThroughTypedefs(const DataType* dt,
                                              const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8 && dt->kind == DataTypeKind::kNamed; ++hops) {
    auto it = typedefs.find(dt->type_name);
    if (it == typedefs.end()) break;
    dt = &it->second;
  }
  return dt;
}

static void ValidateRandAggregateMember(const ClassMember* m,
                                        const TypedefMap& typedefs,
                                        DiagEngine& diag) {
  const DataType* resolved = ResolveThroughTypedefs(&m->data_type, typedefs);
  if (resolved->kind == DataTypeKind::kUnion) {
    if (!resolved->is_packed) {
      diag.Error(m->loc,
                 std::format("unpacked union '{}' takes neither the rand nor "
                             "the randc qualifier",
                             m->name),
                 Subclause("18.4"));
    } else if (resolved->is_tagged) {
      diag.Error(m->loc,
                 std::format("packed tagged union '{}' takes neither the rand "
                             "nor the randc qualifier",
                             m->name),
                 Subclause("18.4"));
    }
    return;
  }
  if (m->is_randc && resolved->kind == DataTypeKind::kStruct &&
      !resolved->is_packed) {
    diag.Error(m->loc,
               std::format("unpacked structure '{}' can be rand but not randc",
                           m->name),
               Subclause("18.4"));
  }
}

void ClassConstraintValidator::ValidateOneClassRandomVariables(
    const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    const DataType& dt = m->data_type;

    if (m->is_randc && IsRealDataType(dt.kind)) {
      diag_.Error(
          m->loc,
          std::format("real variable '{}' can be rand but not randc", m->name),
          Subclause("18.4"));
    }

    if (m->is_randc && dt.kind == DataTypeKind::kNamed &&
        FindClassDecl(dt.type_name, unit_) != nullptr) {
      diag_.Error(
          m->loc,
          std::format("object handle '{}' can be rand but not randc", m->name),
          Subclause("18.4"));
    }

    if (m->is_rand || m->is_randc)
      ValidateRandAggregateMember(m, typedefs_, diag_);
  }
}

void ClassConstraintValidator::ValidateRandomVariableTypes() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassRandomVariables(cls);
}

void ClassConstraintValidator::ValidateOneClassConstraintNames(
    const ClassDecl* cls) {
  std::unordered_set<std::string_view> seen;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (m->name.empty()) continue;
    if (!seen.insert(m->name).second) {
      diag_.Error(m->loc,
                  std::format("constraint block name '{}' is not unique "
                              "within class '{}'",
                              m->name, cls->name),
                  Subclause("18.5"));
    }
  }
}

void ClassConstraintValidator::ValidateConstraintBlockNames() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassConstraintNames(cls);
}

static int ConstraintArrayDimCount(const ClassMember* m) {
  int packed = (m->data_type.packed_dim_left != nullptr ? 1 : 0) +
               static_cast<int>(m->data_type.extra_packed_dims.size());
  int unpacked = static_cast<int>(m->unpacked_dims.size());
  return packed + unpacked;
}

static bool IsFullyVisibleDimensionKind(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return true;
    default:
      return false;
  }
}

static void CheckOneForeachConstraintRef(
    const ConstraintForeachRef& fe,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  auto it = properties.find(fe.array_name);
  if (it == properties.end()) return;
  if (!IsFullyVisibleDimensionKind(it->second->data_type.kind)) return;
  int dims = ConstraintArrayDimCount(it->second);
  if (dims < 1) return;
  if (fe.loop_var_count > dims) {
    diag.Error(
        fe.loc,
        std::format("foreach iterative constraint lists {} loop "
                    "variable(s) but array '{}' has only {} dimension(s)",
                    fe.loop_var_count, fe.array_name, dims),
        Subclause("18.5.7.1"));
  }
}

void ClassConstraintValidator::ValidateOneClassForeachConstraintDims(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& fe : m->constraint_foreach_refs)
      CheckOneForeachConstraintRef(fe, properties, diag_);
  }
}

void ClassConstraintValidator::ValidateForeachConstraintDims() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassForeachConstraintDims(cls);
}

static void CheckOneDistConstraintRef(
    const ConstraintDistRef& ref,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  if (ref.target == nullptr || ref.target->kind != ExprKind::kIdentifier)
    return;
  auto it = properties.find(ref.target->text);
  if (it == properties.end()) return;
  if (it->second->is_randc) {
    diag.Error(ref.target->range.start,
               std::format("a dist constraint may not be applied to randc "
                           "variable '{}'",
                           ref.target->text),
               Subclause("18.5.3"));
  }
  if (!IsRealDataType(it->second->data_type.kind)) return;
  for (const auto& item : ref.items) {
    if (!item.is_range || !item.per_element) continue;
    SourceLoc loc =
        item.lo != nullptr ? item.lo->range.start : ref.target->range.start;
    diag.Error(loc,
               "a real-valued range in a dist constraint requires the :/ "
               "operator and an explicit weight",
               Subclause("18.5.3"));
  }
}

void ClassConstraintValidator::ValidateOneClassDistConstraints(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_dist_refs)
      CheckOneDistConstraintRef(ref, properties, diag_);
  }
}

void ClassConstraintValidator::ValidateDistConstraints() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassDistConstraints(cls);
}

static bool UniqueMemberDenotesVariable(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return e != nullptr && (e->kind == ExprKind::kIdentifier ||
                          e->kind == ExprKind::kMemberAccess);
}

static std::string_view UniqueMemberBaseName(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return (e != nullptr && e->kind == ExprKind::kIdentifier)
             ? e->text
             : std::string_view{};
}

static bool IsSolveOrderableTypeFree(const DataType& dt,
                                     const CompilationUnit* unit) {
  switch (dt.kind) {
    case DataTypeKind::kString:
    case DataTypeKind::kEvent:
    case DataTypeKind::kChandle:
    case DataTypeKind::kVirtualInterface:
    case DataTypeKind::kVoid:
      return false;
    case DataTypeKind::kNamed:
      return FindClassDecl(dt.type_name, unit) == nullptr;
    default:
      return true;
  }
}

static void ValidateOneUniqueConstraintMember(
    const Expr* mem,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (mem == nullptr) return;
  if (!UniqueMemberDenotesVariable(mem)) {
    diag.Error(mem->range.start,
               "a uniqueness constraint member shall denote a singular "
               "or array variable",
               Subclause("18.5.4"));
    return;
  }
  std::string_view base = UniqueMemberBaseName(mem);
  if (base.empty()) return;
  auto it = properties.find(base);
  if (it == properties.end()) return;
  if (it->second->is_randc) {
    diag.Error(mem->range.start,
               "a uniqueness constraint member shall not be a randc variable",
               Subclause("18.5.4"));
  }
  if (!IsSolveOrderableTypeFree(it->second->data_type, unit)) {
    diag.Error(mem->range.start,
               "a uniqueness constraint member shall be of integral or "
               "real type",
               Subclause("18.5.4"));
  }
}

static const DataType* UniqueMemberLeafType(
    const Expr* mem,
    const std::unordered_map<std::string_view, const ClassMember*>&
        properties) {
  const auto kFound = properties.find(UniqueMemberBaseName(mem));
  if (kFound == properties.end()) return nullptr;
  const ClassMember* m = kFound->second;
  const bool kPackedPart =
      mem->kind == ExprKind::kSelect && m->unpacked_dims.empty();
  if (kPackedPart || m->data_type.kind == DataTypeKind::kNamed) return nullptr;
  return &m->data_type;
}

static void ValidateUniqueGroupTypes(
    const std::vector<Expr*>& group,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  const DataType* first = nullptr;
  for (const Expr* mem : group) {
    const DataType* type = UniqueMemberLeafType(mem, properties);
    if (type == nullptr) continue;
    if (first == nullptr) {
      first = type;
    } else if (!TypesEquivalent(*first, *type)) {
      diag.Error(mem->range.start,
                 "the members of a uniqueness constraint shall be of "
                 "equivalent types",
                 Subclause("18.5.4"));
      return;
    }
  }
}

static void ValidateUniqueGroups(
    const ClassMember* block,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag) {
  for (const auto& group : block->constraint_unique_refs) {
    for (const Expr* mem : group)
      ValidateOneUniqueConstraintMember(mem, properties, unit, diag);
    ValidateUniqueGroupTypes(group, properties, diag);
  }
}

void ValidateInlineUniqueGroups(const Expr* call, const ClassDecl* cls,
                                const CompilationUnit* unit, DiagEngine& diag) {
  if (call->inline_constraint == nullptr) return;
  ValidateUniqueGroups(call->inline_constraint,
                       BuildClassPropertyMap(cls, unit), unit, diag);
}

void ClassConstraintValidator::ValidateOneClassUniqueConstraints(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint) {
      ValidateUniqueGroups(m, properties, unit_, diag_);
    }
  }
}

void ClassConstraintValidator::ValidateUniqueConstraints() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassUniqueConstraints(cls);
  ValidateInlineUniqueReceivers(unit_, diag_);
}

struct ConstraintOperandScope {
  std::unordered_map<std::string_view, const ClassMember*> properties;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

static bool PlainlyNeitherIntegralNorReal(const Expr* e,
                                          const ConstraintOperandScope& s) {
  if (e->kind == ExprKind::kCast) return e->text == "string";
  if (e->kind == ExprKind::kIdentifier) {
    const auto kFound = s.properties.find(e->text);
    return kFound != s.properties.end() &&
           !IsSolveOrderableTypeFree(kFound->second->data_type, s.unit);
  }
  if (e->kind == ExprKind::kTernary) {
    return PlainlyNeitherIntegralNorReal(e->true_expr, s) ||
           PlainlyNeitherIntegralNorReal(e->false_expr, s);
  }
  return e->kind == ExprKind::kSystemCall && e->callee == "$sformatf";
}

static bool HoldsRandomVariable(const Expr* e,
                                const ConstraintOperandScope& s) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    const auto kFound = s.properties.find(e->text);
    if (kFound == s.properties.end()) return false;
    const ClassMember* m = kFound->second;
    return (m->is_rand || m->is_randc) &&
           IsSolveOrderableTypeFree(m->data_type, s.unit);
  }
  bool holds = false;
  ForEachExprChild(e, [&](const Expr* child) {
    holds = holds || HoldsRandomVariable(child, s);
  });
  return holds;
}

static void CheckConstraintOperands(const Expr* e,
                                    const ConstraintOperandScope& s) {
  if (e == nullptr) return;
  if (PlainlyNeitherIntegralNorReal(e, s) && HoldsRandomVariable(e, s)) {
    s.diag.Error(e->range.start,
                 "a constraint subexpression holding a random variable shall "
                 "be of an integral or real type",
                 Subclause("18.3"));
    return;
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckConstraintOperands(child, s); });
}

static void ForEachConstraintItemExpr(
    const std::vector<ConstraintItem*>& items,
    const std::function<void(const Expr*)>& fn) {
  for (const ConstraintItem* item : items) {
    fn(item->expr);
    for (const Expr* e : item->exprs) fn(e);
    for (const Expr* e : item->after) fn(e);
    ForEachConstraintItemExpr(item->body, fn);
    ForEachConstraintItemExpr(item->else_body, fn);
  }
}

static bool IsArrayMethodPrimary(const Expr* call,
                                 const ConstraintOperandScope& s) {
  const Expr* access = call->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution ||
      !IsArrayBuiltinMethodName(access->rhs->text)) {
    return false;
  }
  if (access->lhs->kind != ExprKind::kIdentifier) return true;
  const auto kFound = s.properties.find(access->lhs->text);
  if (kFound == s.properties.end()) return true;
  const ClassMember* prop = kFound->second;
  return !prop->unpacked_dims.empty() ||
         (prop->data_type.kind == DataTypeKind::kNamed &&
          FindClassDecl(prop->data_type.type_name, s.unit) == nullptr);
}

static void CheckConstraintPrimaryCall(const Expr* e,
                                       const ConstraintOperandScope& s) {
  if (e->kind != ExprKind::kCall || IsArrayMethodPrimary(e, s)) return;
  s.diag.Error(e->range.start,
               "'()' follows a constraint_primary that is no array built-in "
               "method",
               Subclause("A.1.10"));
}

static void CheckConstraintPrimaryCalls(
    const std::vector<ConstraintItem*>& items,
    const ConstraintOperandScope& s) {
  for (const ConstraintItem* item : items) {
    if (item->kind == ConstraintItemKind::kDisableSoft) {
      CheckConstraintPrimaryCall(item->expr, s);
    } else if (item->kind == ConstraintItemKind::kSolveBefore) {
      for (const Expr* e : item->exprs) CheckConstraintPrimaryCall(e, s);
      for (const Expr* e : item->after) CheckConstraintPrimaryCall(e, s);
    }
    CheckConstraintPrimaryCalls(item->body, s);
    CheckConstraintPrimaryCalls(item->else_body, s);
  }
}

static void CheckConstraintItemOperands(
    const std::vector<ConstraintItem*>& items,
    const ConstraintOperandScope& s) {
  ForEachConstraintItemExpr(
      items, [&s](const Expr* e) { CheckConstraintOperands(e, s); });
  CheckConstraintPrimaryCalls(items, s);
}

void ValidateInlineConstraintOperands(const Expr* call, const ClassDecl* cls,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag) {
  const ConstraintOperandScope kScope{BuildClassPropertyMap(cls, unit), unit,
                                      diag};
  CheckConstraintItemOperands(call->inline_constraint->constraint_items,
                              kScope);
}

static void CheckQualifiedName(const Expr* e, const ClassDecl* cls,
                               const CompilationUnit* unit,
                               const SoleClassIndex& classes,
                               DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kMemberAccess &&
      (e->lhs->text == "this" || e->lhs->text == "super")) {
    const bool kSuper = e->lhs->text == "super";
    const ClassDecl* scope = kSuper ? FindBaseClass(cls, unit) : cls;
    std::unordered_set<std::string_view> names;
    if (scope != nullptr && classes.SelectableNames(*scope, names) &&
        !names.contains(e->rhs->text)) {
      diag.Error(e->range.start,
                 std::format("'{}.{}' names no member of class '{}', the "
                             "class randomize() with is called on{}",
                             e->lhs->text, e->rhs->text, scope->name,
                             kSuper ? " extends" : ""),
                 Subclause("18.7"));
    }
  }
  ForEachExprChild(e, [&](const Expr* child) {
    CheckQualifiedName(child, cls, unit, classes, diag);
  });
}

void ValidateInlineQualifiedNames(const Expr* call, const ClassDecl* cls,
                                  const CompilationUnit* unit,
                                  DiagEngine& diag) {
  const SoleClassIndex kClasses(*unit);
  ForEachConstraintItemExpr(
      call->inline_constraint->constraint_items,
      [&](const Expr* e) { CheckQualifiedName(e, cls, unit, kClasses, diag); });
}

void ClassConstraintValidator::ValidateConstraintOperandTypes() {
  for (const auto* cls : AllClassDecls(unit_)) {
    const ConstraintOperandScope kScope{BuildClassPropertyMap(cls, unit_),
                                        unit_, diag_};
    for (const auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kConstraint) {
        CheckConstraintItemOperands(m->constraint_items, kScope);
      }
    }
  }
}

static void AddSolveBeforeEdges(
    const ConstraintSolveBeforeRef& ref,
    std::unordered_map<std::string_view, std::vector<std::string_view>>& succ,
    std::unordered_set<std::string_view>& nodes) {
  for (const auto& b : ref.before) {
    if (!b.is_simple) continue;
    for (const auto& a : ref.after) {
      if (!a.is_simple) continue;
      succ[b.name].push_back(a.name);
      nodes.insert(b.name);
      nodes.insert(a.name);
    }
  }
}

static bool SolveBeforeVisit(
    std::string_view v,
    const std::unordered_map<std::string_view, std::vector<std::string_view>>&
        succ,
    std::unordered_map<std::string_view, int>& color) {
  color[v] = 1;
  auto sit = succ.find(v);
  if (sit != succ.end()) {
    for (std::string_view w : sit->second) {
      if (color[w] == 1) return true;
      if (color[w] == 0 && SolveBeforeVisit(w, succ, color)) return true;
    }
  }
  color[v] = 2;
  return false;
}

static bool SolveBeforeGraphHasCycle(
    const std::unordered_map<std::string_view, std::vector<std::string_view>>&
        succ,
    const std::unordered_set<std::string_view>& nodes) {
  std::unordered_map<std::string_view, int> color;
  for (std::string_view v : nodes) {
    if (color[v] == 0 && SolveBeforeVisit(v, succ, color)) return true;
  }
  return false;
}

static const ClassMember* ResolveSolveBeforeEntry(
    const ConstraintSolveBeforeEntry& e, const SourceLoc& loc,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  if (!e.is_simple) return nullptr;
  auto it = properties.find(e.name);
  if (it == properties.end()) return nullptr;
  const ClassMember* prop = it->second;
  if (prop->is_randc) {
    diag.Error(loc,
               std::format("randc variable '{}' is not allowed in a "
                           "solve...before ordering constraint",
                           e.name),
               Subclause("18.5.9"));
    return nullptr;
  }
  if (!prop->is_rand) {
    diag.Error(loc,
               std::format("'{}' is not a random variable and cannot "
                           "appear in a solve...before ordering "
                           "constraint",
                           e.name),
               Subclause("18.5.9"));
    return nullptr;
  }
  return prop;
}

struct SolveBeforeOrdering {
  std::unordered_map<std::string_view, std::vector<std::string_view>> succ;
  std::unordered_set<std::string_view> nodes;
  bool have_loc = false;
  SourceLoc report_loc;
};

static void CheckSolveBeforeEntry(
    const ConstraintSolveBeforeEntry& e, const SourceLoc& loc,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag) {
  const ClassMember* prop = ResolveSolveBeforeEntry(e, loc, properties, diag);
  if (prop && !IsSolveOrderableTypeFree(prop->data_type, unit)) {
    diag.Error(loc,
               std::format("solve...before ordering variable '{}' shall be "
                           "of integral or real type",
                           e.name),
               Subclause("18.5.9"));
  }
}

static void CollectSolveBeforeRef(
    const ConstraintSolveBeforeRef& ref,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag, SolveBeforeOrdering& order) {
  if (!order.have_loc) {
    order.report_loc = ref.loc;
    order.have_loc = true;
  }
  for (const auto& e : ref.before)
    CheckSolveBeforeEntry(e, ref.loc, properties, unit, diag);
  for (const auto& e : ref.after)
    CheckSolveBeforeEntry(e, ref.loc, properties, unit, diag);
  AddSolveBeforeEdges(ref, order.succ, order.nodes);
}

void ClassConstraintValidator::ValidateOneClassSolveBeforeConstraints(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  SolveBeforeOrdering order;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_solve_before_refs)
      CollectSolveBeforeRef(ref, properties, unit_, diag_, order);
  }

  if (SolveBeforeGraphHasCycle(order.succ, order.nodes)) {
    diag_.Error(order.report_loc,
                "circular dependency in solve...before variable ordering",
                Subclause("18.5.9"));
  }
}

void ClassConstraintValidator::ValidateSolveBeforeConstraints() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassSolveBeforeConstraints(cls);
}

void ClassConstraintValidator::ValidateOneClassSoftConstraintVariables(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_soft_refs) {
      auto it = properties.find(ref.name);
      if (it == properties.end()) continue;
      if (it->second->is_randc) {
        diag_.Error(ref.loc,
                    std::format("a soft constraint may not be specified on "
                                "randc variable '{}'",
                                ref.name),
                    Subclause("18.5.13.1"));
      }
    }
  }
}

void ClassConstraintValidator::ValidateSoftConstraintVariables() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassSoftConstraintVariables(cls);
}

}  // namespace delta
