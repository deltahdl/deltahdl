#include "elaborator/type_param_scope_prefix.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_restriction.h"
#include "elaborator/type_param_scope_prefix_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool DeclaresTypeParam(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kParamDecl &&
         item.data_type.kind == DataTypeKind::kVoid &&
         item.typedef_type.kind != DataTypeKind::kImplicit;
}

const ModuleItem* TypeParamItem(const std::vector<ModuleItem*>& items,
                                std::string_view name) {
  for (const ModuleItem* item : items) {
    if (DeclaresTypeParam(*item) && item->name == name) return item;
  }
  return nullptr;
}

const ModuleItem* PackageTypeParam(std::string_view package,
                                   std::string_view name,
                                   const CompilationUnit* unit) {
  for (const PackageDecl* pkg : unit->packages) {
    if (pkg->name == package) return TypeParamItem(pkg->items, name);
  }
  return nullptr;
}

const ModuleItem* ScopeTypeParam(std::string_view scope, std::string_view name,
                                 const CompilationUnit* unit) {
  if (scope == "$unit") return TypeParamItem(unit->cu_items, name);
  return PackageTypeParam(scope, name, unit);
}

const DataType* ItemType(const ModuleItem* item) {
  return item != nullptr ? &item->typedef_type : nullptr;
}

const DataType* NextTypeName(const DataType& type,
                             const TypeParamPrefixScope& scope) {
  auto next = scope.typedefs.find(TypeChainKey(type));
  if (next != scope.typedefs.end()) return &next->second;
  return ItemType(ScopeTypeParam(type.scope_name, type.type_name, scope.unit));
}

}  // namespace

static bool MayBeClass(const DataType& type,
                       const TypeParamPrefixScope& scope) {
  const DataType* cur = &type;
  for (int depth = 0; depth < 32; ++depth) {
    if (cur->kind != DataTypeKind::kNamed) return false;
    if (scope.class_names.contains(TypeChainKey(*cur))) return true;
    const DataType* next = NextTypeName(*cur, scope);
    if (next == nullptr) return true;
    cur = next;
  }
  return true;
}

static void EmitPrefixNotAClass(std::string_view prefix, SourceLoc loc,
                                DiagEngine& diag) {
  diag.ErrorOnce(loc,
                 std::format("type parameter '{}' used as a class scope "
                             "resolution prefix does not resolve to a class",
                             prefix),
                 Subclause("6.20.3"));
}

static bool IsTypeParamOf(const std::vector<RtlirParamDecl>& params,
                          std::string_view name) {
  return std::ranges::any_of(params, [&](const RtlirParamDecl& p) {
    return p.is_type_param && p.name == name;
  });
}

void ReportTypeParamPrefixNotAClass(std::string_view prefix, SourceLoc loc,
                                    const TypeParamPrefixScope& scope,
                                    DiagEngine& diag) {
  if (prefix.empty() || !IsTypeParamOf(scope.params, prefix)) return;
  auto bound = scope.typedefs.find(prefix);
  if (bound == scope.typedefs.end() || MayBeClass(bound->second, scope)) return;
  EmitPrefixNotAClass(prefix, loc, diag);
}

namespace {

struct LocalTypeName {
  std::string_view name;
  const DataType* bound;
  bool is_param;
  bool bound_per_specialization = false;
};

using LocalTypeNames = std::vector<LocalTypeName>;

struct PrefixWalk {
  const TypeParamPrefixScope* outer;
  const TypeParamRestrictionScope& restriction;
  DiagEngine& diag;
  bool outer_type_refs = false;
};

const LocalTypeName* FindLocal(const LocalTypeNames& locals,
                               std::string_view name) {
  for (auto it = locals.rbegin(); it != locals.rend(); ++it) {
    if (it->name == name) return &*it;
  }
  return nullptr;
}

bool UnitTypeIsNoClass(const DataType& type, const PrefixWalk& walk) {
  static const std::vector<RtlirParamDecl> kNoParams;
  return !MayBeClass(
      type, {kNoParams, walk.restriction.typedefs, walk.restriction.class_names,
             walk.restriction.unit});
}

bool BoundToNoClass(const LocalTypeName& local, const LocalTypeNames& locals,
                    const PrefixWalk& walk) {
  if (local.bound_per_specialization) return false;
  const DataType* cur = local.bound;
  for (int depth = 0; depth < 32; ++depth) {
    if (cur->kind == DataTypeKind::kImplicit) return false;
    if (cur->kind != DataTypeKind::kNamed) return true;
    const LocalTypeName* next =
        cur->scope_name.empty() ? FindLocal(locals, cur->type_name) : nullptr;
    if (next == nullptr) return UnitTypeIsNoClass(*cur, walk);
    if (next->bound_per_specialization) return false;
    cur = next->bound;
  }
  return false;
}

void JudgePrefix(std::string_view prefix, SourceLoc loc,
                 const LocalTypeNames& locals, const PrefixWalk& walk,
                 bool outer_too) {
  if (prefix.empty()) return;
  if (const LocalTypeName* local = FindLocal(locals, prefix)) {
    if (local->is_param && BoundToNoClass(*local, locals, walk))
      EmitPrefixNotAClass(prefix, loc, walk.diag);
    return;
  }
  if (outer_too && walk.outer != nullptr)
    ReportTypeParamPrefixNotAClass(prefix, loc, *walk.outer, walk.diag);
}

bool NamesTypeParam(std::string_view name, const LocalTypeNames& locals,
                    const PrefixWalk& walk) {
  if (name.empty()) return false;
  if (const LocalTypeName* local = FindLocal(locals, name))
    return local->is_param;
  return walk.outer != nullptr && IsTypeParamOf(walk.outer->params, name);
}

const ModuleItem* ClassBodyTypeParam(const ClassDecl& cls,
                                     std::string_view name) {
  for (const ClassMember* m : cls.members) {
    if (DeclaresBodyTypeParam(*m) && m->typedef_item->name == name)
      return m->typedef_item;
  }
  return nullptr;
}

const DataType* BodyParamType(const ClassDecl& cls, std::string_view name) {
  return ItemType(ClassBodyTypeParam(cls, name));
}

size_t ParamIndex(const ClassDecl& cls, std::string_view name) {
  auto param = std::ranges::find(cls.params, name,
                                 &std::pair<std::string_view, Expr*>::first);
  return static_cast<size_t>(param - cls.params.begin());
}

const DataType* OuterScopeParamType(const DataType& type,
                                    const CompilationUnit* unit) {
  std::string_view outer = type.outer_scope_names.back();
  std::string_view name = type.scope_name;
  if (const ModuleItem* item = ScopeTypeParam(outer, name, unit))
    return &item->typedef_type;
  const ClassDecl* cls = FindClassDecl(outer, unit);
  if (cls == nullptr) return nullptr;
  if (!cls->type_param_names.contains(name)) return BodyParamType(*cls, name);
  return BoundActual(*cls, ParamIndex(*cls, name), name, type);
}

bool SelectsTypeThroughTypeParam(const DataType& type,
                                 const LocalTypeNames& locals,
                                 const PrefixWalk& walk) {
  if (type.kind != DataTypeKind::kNamed || type.scope_name.empty())
    return false;
  if (type.outer_scope_names.empty())
    return NamesTypeParam(type.scope_name, locals, walk);
  return OuterScopeParamType(type, walk.restriction.unit) != nullptr;
}

const DataType* PrefixBinding(std::string_view prefix,
                              const LocalTypeNames& locals,
                              const PrefixWalk& walk) {
  if (const LocalTypeName* local = FindLocal(locals, prefix))
    return local->bound;
  if (walk.outer == nullptr) return nullptr;
  auto bound = walk.outer->typedefs.find(prefix);
  return bound == walk.outer->typedefs.end() ? nullptr : &bound->second;
}

constexpr std::array<std::string_view, 13> kTypeKeywords = {
    "bit",      "byte", "int",      "integer",   "logic",  "longint", "real",
    "realtime", "reg",  "shortint", "shortreal", "string", "time"};

PrefixBound ArgumentBound(const Expr* arg) {
  if (arg->kind == ExprKind::kTypeRef) return PrefixBoundOf(arg->type_value);
  if (std::ranges::find(kTypeKeywords, arg->text) != kTypeKeywords.end())
    return {PrefixBoundKind::kNoClass, {}, nullptr};
  return {PrefixBoundKind::kNamed, arg->text, nullptr};
}

const Expr* SpecializationArgument(const Expr* spec, size_t i,
                                   std::string_view name) {
  if (!spec->arg_names.empty() && !spec->arg_names[0].empty()) {
    auto named = std::ranges::find(spec->arg_names, name);
    if (named == spec->arg_names.end()) return nullptr;
    return spec->elements[named - spec->arg_names.begin()];
  }
  return i < spec->elements.size() ? spec->elements[i] : nullptr;
}

PrefixBound ClassParamBound(const ClassDecl& cls, std::string_view name,
                            const Expr* spec) {
  if (!cls.type_param_names.contains(name))
    return PrefixBoundOf(BodyParamType(cls, name));
  size_t i = ParamIndex(cls, name);
  const Expr* arg = SpecializationArgument(spec, i, name);
  return arg != nullptr ? ArgumentBound(arg)
                        : PrefixBoundOf(&cls.param_types[i]);
}

PrefixBound OutsideBound(const Expr* scope, const CompilationUnit* unit) {
  if (scope->kind == ExprKind::kIdentifier)
    return PrefixBoundOf(ItemType(TypeParamItem(unit->cu_items, scope->text)));
  if (!SelectsThroughName(scope)) return {};
  std::string_view outer = scope->lhs->text;
  std::string_view name = scope->rhs->text;
  if (const ModuleItem* item = PackageTypeParam(outer, name, unit))
    return PrefixBoundOf(&item->typedef_type);
  const ClassDecl* cls = FindClassDecl(outer, unit);
  return cls != nullptr ? ClassParamBound(*cls, name, scope->lhs)
                        : PrefixBound{};
}

bool IsNoClass(const PrefixBound& bound, const PrefixWalk& walk) {
  if (bound.kind != PrefixBoundKind::kNamed)
    return bound.kind == PrefixBoundKind::kNoClass;
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.type_name = bound.name;
  return UnitTypeIsNoClass(bound.type != nullptr ? *bound.type : named, walk);
}

std::string_view OutsideName(const Expr* scope) {
  return scope->kind == ExprKind::kIdentifier ? scope->text : scope->rhs->text;
}

void JudgeOutsidePrefix(const Expr* scope, SourceLoc loc,
                        const PrefixWalk& walk) {
  if (IsNoClass(OutsideBound(scope, walk.restriction.unit), walk))
    EmitPrefixNotAClass(OutsideName(scope), loc, walk.diag);
}

PrefixBound ScopeBound(const Expr* scope, const LocalTypeNames& locals,
                       const PrefixWalk& walk) {
  if (!NamesLocalScope(scope))
    return OutsideBound(scope, walk.restriction.unit);
  return PrefixBoundOf(PrefixBinding(scope->text, locals, walk));
}

bool SelectsAType(const Expr* e, const LocalTypeNames& locals,
                  const PrefixWalk& walk) {
  PrefixBound bound = ScopeBound(e->lhs, locals, walk);
  if (bound.kind != PrefixBoundKind::kNamed) return false;
  const ClassDecl* cls = BoundClass(bound, walk.restriction.unit);
  return cls != nullptr && ClassDeclaresType(*cls, e->rhs->text);
}

void JudgeTypeOperand(const Expr* e, const LocalTypeNames& locals,
                      const PrefixWalk& walk) {
  if (!IsScopeSelection(e) || !SelectsAType(e, locals, walk)) return;
  const Expr* scope = e->lhs;
  if (!NamesLocalScope(scope)) {
    EmitPrefixRestricted(OutsideName(scope), e->range.start, walk.diag);
  } else if (NamesTypeParam(scope->text, locals, walk)) {
    EmitPrefixRestricted(scope->text, scope->range.start, walk.diag);
  }
}

void JudgeSelection(const Expr* e, const LocalTypeNames& locals,
                    const PrefixWalk& walk) {
  const Expr* scope = e->lhs;
  if (NamesLocalScope(scope)) {
    JudgePrefix(scope->text, scope->range.start, locals, walk, true);
    return;
  }
  JudgeOutsidePrefix(scope, e->range.start, walk);
}

void JudgeTypeName(const DataType& type, SourceLoc loc,
                   const LocalTypeNames& locals, const PrefixWalk& walk);

void JudgeNestedSelections(const Expr* e, const LocalTypeNames& locals,
                           const PrefixWalk& walk);

bool JudgesTypeOperator(const Expr* e, const LocalTypeNames& locals,
                        const PrefixWalk& walk) {
  if (e->kind != ExprKind::kTypeRef) return false;
  if (e->type_value != nullptr)
    JudgeTypeName(*e->type_value, e->range.start, locals, walk);
  JudgeNestedSelections(e->lhs, locals, walk);
  return true;
}

void JudgeExpr(const Expr* e, const LocalTypeNames& locals,
               const PrefixWalk& walk) {
  if (e == nullptr || JudgesTypeOperator(e, locals, walk)) return;
  if (e->kind == ExprKind::kCast && e->rhs != nullptr)
    JudgeTypeOperand(e->rhs, locals, walk);
  if (QueriesAType(e)) JudgeTypeOperand(e->args[0], locals, walk);
  if (IsScopeSelection(e)) JudgeSelection(e, locals, walk);
  ForEachExprChild(e,
                   [&](const Expr* child) { JudgeExpr(child, locals, walk); });
}

void JudgeNestedSelections(const Expr* e, const LocalTypeNames& locals,
                           const PrefixWalk& walk) {
  if (e == nullptr || JudgesTypeOperator(e, locals, walk)) return;
  if (IsScopeSelection(e)) JudgeSelection(e, locals, walk);
  ForEachExprChild(e, [&](const Expr* child) {
    JudgeNestedSelections(child, locals, walk);
  });
}

void JudgeTypeRef(const DataType& type, SourceLoc loc,
                  const LocalTypeNames& locals, const PrefixWalk& walk) {
  const Expr* ref = type.type_ref_expr;
  if (ref == nullptr) return;
  if (!IsScopeSelection(ref)) {
    JudgeNestedSelections(ref, locals, walk);
    return;
  }
  if (NamesLocalScope(ref->lhs)) {
    JudgePrefix(ref->lhs->text, loc, locals, walk, walk.outer_type_refs);
    return;
  }
  JudgeOutsidePrefix(ref->lhs, loc, walk);
}

void JudgeTypedPrefix(const DataType& type, SourceLoc loc,
                      const LocalTypeNames& locals, const PrefixWalk& walk) {
  if (type.outer_scope_names.empty()) {
    JudgePrefix(type.scope_name, loc, locals, walk, true);
  } else if (IsNoClass(PrefixBoundOf(
                           OuterScopeParamType(type, walk.restriction.unit)),
                       walk)) {
    EmitPrefixNotAClass(type.scope_name, loc, walk.diag);
  }
}

const DataType* ArgumentPrefixBinding(const DataType& arg,
                                      const LocalTypeNames& locals,
                                      const PrefixWalk& walk) {
  if (!arg.outer_scope_names.empty())
    return OuterScopeParamType(arg, walk.restriction.unit);
  return PrefixBinding(arg.scope_name, locals, walk);
}

bool ArgumentSelectsAType(const DataType& arg, const LocalTypeNames& locals,
                          const PrefixWalk& walk) {
  const ClassDecl* cls =
      BoundClass(PrefixBoundOf(ArgumentPrefixBinding(arg, locals, walk)),
                 walk.restriction.unit);
  return cls != nullptr && ClassDeclaresType(*cls, arg.type_name);
}

void JudgeArguments(const std::vector<DataType>& args, SourceLoc loc,
                    const LocalTypeNames& locals, const PrefixWalk& walk,
                    bool restricted) {
  for (const DataType& arg : args) {
    if (restricted) {
      JudgeExpr(arg.type_ref_expr, locals, walk);
    } else {
      JudgeNestedSelections(arg.type_ref_expr, locals, walk);
    }
    if (!arg.scope_name.empty()) {
      JudgeTypedPrefix(arg, loc, locals, walk);
      if (restricted && SelectsTypeThroughTypeParam(arg, locals, walk) &&
          ArgumentSelectsAType(arg, locals, walk))
        EmitPrefixRestricted(arg.scope_name, loc, walk.diag);
    }
    JudgeArguments(arg.type_params, loc, locals, walk, restricted);
  }
}

void JudgeTypeName(const DataType& type, SourceLoc loc,
                   const LocalTypeNames& locals, const PrefixWalk& walk) {
  JudgeTypedPrefix(type, loc, locals, walk);
  JudgeTypeRef(type, loc, locals, walk);
  JudgeArguments(type.type_params, loc, locals, walk, false);
}

void JudgeDeclaredType(const DataType& type, SourceLoc loc,
                       const LocalTypeNames& locals, const PrefixWalk& walk) {
  if (SelectsTypeThroughTypeParam(type, locals, walk))
    EmitPrefixRestricted(type.scope_name, loc, walk.diag);
  JudgeArguments(type.type_params, loc, locals, walk, true);
  for (const StructMember& member : type.struct_members) {
    if (NamesTypeParam(member.scope_name, locals, walk))
      EmitPrefixRestricted(member.scope_name, loc, walk.diag);
    JudgeArguments(member.type_params, loc, locals, walk, true);
  }
}

void JudgeOverrides(const ModuleItem& item, const LocalTypeNames& locals,
                    const PrefixWalk& walk) {
  for (const auto& [name, value] : item.inst_params) {
    JudgeExpr(value, locals, walk);
    if (value != nullptr) JudgeTypeOperand(value, locals, walk);
  }
}

bool NamesLocal(const DataType& type, const LocalTypeName& local) {
  return type.kind == DataTypeKind::kNamed && type.scope_name.empty() &&
         type.type_name == local.name;
}

void JudgeRestriction(const ModuleItem& item, const LocalTypeNames& locals,
                      const PrefixWalk& walk) {
  const DataType* bound = &item.typedef_type;
  for (auto it = locals.rbegin(); it != locals.rend(); ++it) {
    if (NamesLocal(*bound, *it)) bound = it->bound;
  }
  ReportTypeOutsideRestriction({item.name, item.forward_type_kind}, *bound,
                               item.loc, walk.restriction, walk.diag);
}

void DeclareTypeName(const ModuleItem& item, bool is_param,
                     LocalTypeNames& locals, const PrefixWalk& walk) {
  JudgeTypeName(item.typedef_type, item.loc, locals, walk);
  if (is_param) JudgeRestriction(item, locals, walk);
  locals.push_back({item.name, &item.typedef_type, is_param});
}

void JudgeSubroutineHeader(const ModuleItem& item, const LocalTypeNames& locals,
                           const PrefixWalk& walk) {
  JudgeDeclaredType(item.return_type, item.loc, locals, walk);
  for (const FunctionArg& arg : item.func_args)
    JudgeDeclaredType(arg.data_type, item.loc, locals, walk);
}

bool DeclaresData(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kVarDecl ||
         item.kind == ModuleItemKind::kNetDecl ||
         item.kind == ModuleItemKind::kParamDecl;
}

void JudgeItemSelections(const ModuleItem& item, const LocalTypeNames& locals,
                         const PrefixWalk& walk) {
  if (DeclaresData(item)) {
    JudgeDeclaredType(item.data_type, item.loc, locals, walk);
    JudgeExpr(item.init_expr, locals, walk);
  } else if (item.kind == ModuleItemKind::kContAssign) {
    JudgeExpr(item.assign_lhs, locals, walk);
    JudgeExpr(item.assign_rhs, locals, walk);
  } else if (item.kind == ModuleItemKind::kFunctionDecl ||
             item.kind == ModuleItemKind::kTaskDecl) {
    JudgeSubroutineHeader(item, locals, walk);
  } else if (item.kind == ModuleItemKind::kModuleInst) {
    JudgeOverrides(item, locals, walk);
  }
}

void WalkStmt(Stmt* s, LocalTypeNames& locals, const PrefixWalk& walk) {
  if (s == nullptr) return;
  const ModuleItem* item = s->decl_item;
  if (s->kind == StmtKind::kBlockItemDecl && item != nullptr &&
      item->kind == ModuleItemKind::kTypedef) {
    DeclareTypeName(*item, false, locals, walk);
  } else if (s->kind == StmtKind::kVarDecl && s->var_is_param &&
             item != nullptr && DeclaresTypeParam(*item)) {
    DeclareTypeName(*item, true, locals, walk);
  } else if (s->kind == StmtKind::kVarDecl) {
    JudgeTypeRef(s->var_decl_type, s->range.start, locals, walk);
    JudgeDeclaredType(s->var_decl_type, s->range.start, locals, walk);
  }
  ForEachChildExpr(s, [&](const Expr* e) { JudgeExpr(e, locals, walk); });
  LocalTypeNames inner = locals;
  ForEachChildStmt(s, [&](Stmt* sub) { WalkStmt(sub, inner, walk); });
}

void WalkProcedure(const ModuleItem& item, const LocalTypeNames& locals,
                   const PrefixWalk& walk) {
  LocalTypeNames inner = locals;
  WalkStmt(item.body, inner, walk);
  for (Stmt* s : item.func_body_stmts) WalkStmt(s, inner, walk);
}

bool DeclaresChecker(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kNestedModuleDecl &&
         item.nested_module_decl != nullptr &&
         item.nested_module_decl->decl_kind == ModuleDeclKind::kChecker;
}

bool HoldsStatements(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kFunctionDecl ||
         item.kind == ModuleItemKind::kTaskDecl ||
         IsProceduralItemKind(item.kind);
}

void WalkScopeItems(const std::vector<ModuleItem*>& items,
                    LocalTypeNames locals, const PrefixWalk& walk);

void WalkGenerateBlocks(const ModuleItem& item, const LocalTypeNames& locals,
                        const PrefixWalk& walk) {
  WalkScopeItems(item.gen_body, locals, walk);
  if (item.gen_else != nullptr) WalkScopeItems({item.gen_else}, locals, walk);
  for (const GenerateCaseItem& branch : item.gen_case_items)
    WalkScopeItems(branch.body, locals, walk);
}

void WalkScopeItem(const ModuleItem& item, LocalTypeNames& locals,
                   const PrefixWalk& walk) {
  if (item.kind == ModuleItemKind::kTypedef) {
    DeclareTypeName(item, false, locals, walk);
    return;
  }
  if (DeclaresTypeParam(item)) {
    DeclareTypeName(item, true, locals, walk);
    return;
  }
  JudgeItemSelections(item, locals, walk);
  if (item.kind == ModuleItemKind::kVarDecl) {
    JudgeTypeRef(item.data_type, item.loc, locals, walk);
  } else if (HoldsStatements(item)) {
    WalkProcedure(item, locals, walk);
  } else if (DeclaresChecker(item)) {
    WalkScopeItems(item.nested_module_decl->items, {}, walk);
  } else {
    WalkGenerateBlocks(item, locals, walk);
  }
}

void WalkScopeItems(const std::vector<ModuleItem*>& items,
                    LocalTypeNames locals, const PrefixWalk& walk) {
  for (const ModuleItem* item : items) WalkScopeItem(*item, locals, walk);
}

LocalTypeNames ClassTypeNames(const ClassDecl& cls) {
  LocalTypeNames locals;
  for (size_t i = 0; i < cls.params.size(); ++i) {
    if (cls.type_param_names.contains(cls.params[i].first))
      locals.push_back({cls.params[i].first, &cls.param_types[i], true, true});
  }
  for (const ClassMember* m : cls.members) {
    if (m->kind == ClassMemberKind::kTypedef)
      locals.push_back({m->name, &m->typedef_item->typedef_type,
                        m->typedef_item->is_localparam});
  }
  return locals;
}

void WalkClassMember(const ClassMember& m, const LocalTypeNames& locals,
                     const PrefixWalk& walk) {
  if (m.kind == ClassMemberKind::kTypedef) {
    JudgeTypeName(m.typedef_item->typedef_type, m.loc, locals, walk);
  } else if (m.kind == ClassMemberKind::kProperty && !m.is_param) {
    JudgeDeclaredType(m.data_type, m.loc, locals, walk);
    JudgeTypeRef(m.data_type, m.loc, locals, walk);
    JudgeExpr(m.init_expr, locals, walk);
  } else if (m.kind == ClassMemberKind::kConstraint) {
    for (const Expr* e : m.constraint_exprs) JudgeExpr(e, locals, walk);
  } else if (m.method != nullptr) {
    JudgeSubroutineHeader(*m.method, locals, walk);
    WalkProcedure(*m.method, locals, walk);
  }
}

void WalkClass(const ClassDecl& cls, const PrefixWalk& walk) {
  const LocalTypeNames kLocals = ClassTypeNames(cls);
  for (size_t i = 0; i < cls.params.size(); ++i) {
    if (cls.type_param_names.contains(cls.params[i].first))
      JudgeTypedPrefix(cls.param_types[i], cls.param_port_locs[i], kLocals,
                       walk);
  }
  for (const std::vector<DataType>* args : BaseArgumentLists(cls))
    JudgeArguments(*args, cls.range.start, kLocals, walk, true);
  for (const Expr* arg : cls.extends_args) JudgeExpr(arg, kLocals, walk);
  for (const ClassMember* m : cls.members) WalkClassMember(*m, kLocals, walk);
}

}  // namespace

void ReportItemTypeParamErrors(const ModuleItem& item,
                               const TypeParamPrefixScope& scope,
                               const TypeParamRestrictionScope& restriction,
                               DiagEngine& diag) {
  if (DeclaresChecker(item)) {
    WalkScopeItems(item.nested_module_decl->items, {},
                   {&scope, restriction, diag, true});
    return;
  }
  const PrefixWalk kWalk{&scope, restriction, diag};
  if (item.kind == ModuleItemKind::kTypedef || DeclaresTypeParam(item)) {
    JudgeTypeName(item.typedef_type, item.loc, {}, kWalk);
    return;
  }
  if (item.kind == ModuleItemKind::kVarDecl)
    JudgeTypeRef(item.data_type, item.loc, {}, kWalk);
  JudgeItemSelections(item, {}, kWalk);
  WalkProcedure(item, {}, kWalk);
}

static bool KeepsDefault(const std::vector<RtlirParamDecl>& params,
                         std::string_view name, const DataType& written) {
  const std::string kWritten = TypeChainKey(written);
  return std::ranges::any_of(params, [&](const RtlirParamDecl& param) {
    return param.name == name && TypeChainKey(*param.resolved_type) == kWritten;
  });
}

void ReportPortTypeParamErrors(const ModuleDecl& decl,
                               const TypeParamPrefixScope& scope,
                               const TypeParamRestrictionScope& restriction,
                               DiagEngine& diag) {
  const PrefixWalk kWalk{&scope, restriction, diag};
  for (const PortDecl& port : decl.ports)
    JudgeDeclaredType(port.data_type, port.loc, {}, kWalk);
  for (size_t i = 0; i < decl.param_types.size(); ++i) {
    const DataType& written = decl.param_types[i];
    std::string_view name = decl.params[i].first;
    if (decl.type_param_names.contains(name) && !written.scope_name.empty() &&
        KeepsDefault(scope.params, name, written))
      JudgeTypedPrefix(written, decl.param_port_locs[i], {}, kWalk);
  }
}

void ReportUnitScopeTypeParamErrors(const TypeParamRestrictionScope& scope,
                                    DiagEngine& diag) {
  const PrefixWalk kWalk{nullptr, scope, diag};
  for (const PackageDecl* pkg : scope.unit->packages)
    WalkScopeItems(pkg->items, {}, kWalk);
  WalkScopeItems(scope.unit->cu_items, {}, kWalk);
  for (const ModuleDecl* checker : scope.unit->checkers)
    WalkScopeItems(checker->items, {}, kWalk);
  for (const ClassDecl* cls : AllClassDecls(scope.unit)) WalkClass(*cls, kWalk);
}

void ReportTypeRefPrefixNotAClass(const Expr* ref, SourceLoc loc,
                                  const TypeParamPrefixScope& scope,
                                  DiagEngine& diag) {
  if (ref->kind != ExprKind::kMemberAccess || !ref->is_scope_resolution ||
      ref->lhs == nullptr || ref->lhs->kind != ExprKind::kIdentifier)
    return;
  ReportTypeParamPrefixNotAClass(ref->lhs->text, loc, scope, diag);
}

const DataType* TypeRefThroughBoundPrefix(std::string_view prefix,
                                          std::string_view name,
                                          const TypedefMap& typedefs) {
  DataType written;
  written.kind = DataTypeKind::kNamed;
  written.scope_name = prefix;
  written.type_name = name;
  if (!ThroughBoundPrefix(written, typedefs).has_value()) return nullptr;
  return FindNamedType(written, typedefs);
}

constexpr std::array<std::string_view, 10> kTypeQueryFunctions = {
    "$bits", "$typename",  "$left", "$right",      "$low",
    "$high", "$increment", "$size", "$dimensions", "$unpacked_dimensions"};

bool DeclaresBodyTypeParam(const ClassMember& m) {
  return m.kind == ClassMemberKind::kTypedef && m.typedef_item->is_localparam;
}

const DataType* BoundActual(const ClassDecl& cls, size_t i,
                            std::string_view name, const DataType& written) {
  const DataType* actual = SpecializationArgument(written.type_params, i, name);
  return actual != nullptr ? actual : &cls.param_types[i];
}

bool IsScopeSelection(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess && e->is_scope_resolution;
}

bool SelectsThroughName(const Expr* e) {
  return IsScopeSelection(e) && e->lhs->kind == ExprKind::kIdentifier;
}

bool ClassDeclaresType(const ClassDecl& cls, std::string_view name) {
  return std::ranges::any_of(cls.members, [&](const ClassMember* m) {
    return m->name == name && (m->kind == ClassMemberKind::kClassDecl ||
                               m->kind == ClassMemberKind::kTypedef);
  });
}

PrefixBound PrefixBoundOf(const DataType* type) {
  if (type == nullptr || type->kind == DataTypeKind::kImplicit) return {};
  if (type->kind != DataTypeKind::kNamed)
    return {PrefixBoundKind::kNoClass, {}, nullptr};
  return {PrefixBoundKind::kNamed, type->type_name, type};
}

bool NamesLocalScope(const Expr* scope) {
  return scope->kind == ExprKind::kIdentifier && scope->scope_prefix.empty();
}

const ClassDecl* BoundClass(const PrefixBound& bound,
                            const CompilationUnit* unit) {
  if (bound.type == nullptr || bound.type->scope_name == "$unit")
    return FindClassDecl(bound.name, unit);
  return ClassOfDeclaredType(*bound.type, {}, unit);
}

std::vector<const std::vector<DataType>*> BaseArgumentLists(
    const ClassDecl& cls) {
  std::vector<const std::vector<DataType>*> lists{&cls.base_class_type_params};
  for (const InterfaceRef& base : cls.extends_interfaces)
    lists.push_back(&base.type_params);
  for (const InterfaceRef& base : cls.implements_types)
    lists.push_back(&base.type_params);
  return lists;
}

bool QueriesAType(const Expr* e) {
  return e->kind == ExprKind::kSystemCall && !e->args.empty() &&
         std::ranges::find(kTypeQueryFunctions, e->callee) !=
             kTypeQueryFunctions.end();
}

void EmitPrefixRestricted(std::string_view prefix, SourceLoc loc,
                          DiagEngine& diag) {
  diag.ErrorOnce(loc,
                 std::format("type parameter '{}' {}", prefix,
                             kPermittedScopePrefixContexts),
                 Subclause("6.20.3"));
}

}  // namespace delta
