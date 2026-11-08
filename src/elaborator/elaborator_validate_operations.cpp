#include "elaborator/elaborator_validate_operations.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <span>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/scope_value_type.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_ref_dynamic_element.h"
#include "elaborator/type_ref_walks.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

NetType DataTypeToNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kTri:
      return NetType::kTri;
    case DataTypeKind::kWand:
      return NetType::kWand;
    case DataTypeKind::kWor:
      return NetType::kWor;
    case DataTypeKind::kTriand:
      return NetType::kTriand;
    case DataTypeKind::kTrior:
      return NetType::kTrior;
    case DataTypeKind::kTri0:
      return NetType::kTri0;
    case DataTypeKind::kTri1:
      return NetType::kTri1;
    case DataTypeKind::kSupply0:
      return NetType::kSupply0;
    case DataTypeKind::kSupply1:
      return NetType::kSupply1;
    case DataTypeKind::kTrireg:
      return NetType::kTrireg;
    case DataTypeKind::kUwire:
      return NetType::kUwire;
    default:
      return NetType::kWire;
  }
}

NetType WrittenNetType(const DataType& dtype) {
  if (dtype.is_interconnect) return NetType::kInterconnect;
  return DataTypeToNetType(dtype.net_keyword != DataTypeKind::kImplicit
                               ? dtype.net_keyword
                               : dtype.kind);
}

static std::string_view AggregateOperandName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kSelect &&
      (e->index_end || e->is_part_select_plus || e->is_part_select_minus) &&
      e->base && e->base->kind == ExprKind::kIdentifier) {
    return e->base->text;
  }
  return {};
}

using NameMap = std::unordered_map<std::string_view, std::string_view>;
using WidthMap = std::unordered_map<std::string_view, uint32_t>;

static bool CheckArrayCompareOp(const Expr* expr, const NameMap& types,
                                const WidthMap& widths, DiagEngine& diag) {
  if (expr->lhs->kind != ExprKind::kIdentifier ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto lt = types.find(AggregateOperandName(expr->lhs));
  auto rt = types.find(AggregateOperandName(expr->rhs));
  if (lt == types.end() || rt == types.end()) return false;
  auto lw = widths.find(lt->second);
  auto rw = widths.find(rt->second);
  if (lw == widths.end() || rw == widths.end()) return false;
  if (lw->second != rw->second) {
    diag.Error(expr->range.start,
               "comparison of non-equivalent aggregate array types",
               Subclause("6.22.2"));
  }
  return true;
}

bool ElaboratorOperationRules::ReportNonEquivalentArrayOperands(
    const Expr* expr) {
  auto equivalent = ArrayOperandsEquivalent(expr->lhs, expr->rhs);
  if (!equivalent) return false;
  if (!*equivalent) {
    diag_.Error(expr->range.start,
                "comparison of non-equivalent aggregate array types",
                Subclause("6.22.2"));
  }
  return true;
}

void ElaboratorOperationRules::CheckAggregateCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  auto l_name = AggregateOperandName(expr->lhs);
  auto r_name = AggregateOperandName(expr->rhs);
  if (l_name.empty() || r_name.empty()) return;
  if (ReportNonEquivalentArrayOperands(expr)) return;
  if (CheckArrayCompareOp(expr, var_named_types_,
                          fixed_unpacked_typedef_widths_, diag_)) {
    return;
  }

  auto lit = var_named_types_.find(l_name);
  auto rit = var_named_types_.find(r_name);
  if (lit == var_named_types_.end() || rit == var_named_types_.end()) return;
  if (lit->second == rit->second) return;

  auto is_aggregate_var = [&](std::string_view name,
                              std::string_view type_name) {
    if (var_array_info_.count(name)) return true;
    auto it = typedefs_.find(type_name);
    return it != typedefs_.end() && IsAggregateType(it->second);
  };
  if (!is_aggregate_var(l_name, lit->second)) return;
  if (!is_aggregate_var(r_name, rit->second)) return;

  diag_.Error(expr->range.start,
              std::format("comparison of non-equivalent aggregate "
                          "types '{}' and '{}'",
                          lit->second, rit->second),
              Subclause("6.22.2"));
}

void ElaboratorOperationRules::WalkExprForAggregateCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary &&
      (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq)) {
    CheckAggregateCompareOp(expr);
  }
  if (expr->kind == ExprKind::kTernary &&
      !ArrayOperandsEquivalent(expr->true_expr, expr->false_expr)
           .value_or(true)) {
    diag_.Error(expr->range.start,
                "the operands of a conditional operator shall be of "
                "equivalent types",
                Subclause("11.4.11"));
  }
  WalkExprForAggregateCompare(expr->lhs);
  WalkExprForAggregateCompare(expr->rhs);
  WalkExprForAggregateCompare(expr->condition);
  WalkExprForAggregateCompare(expr->true_expr);
  WalkExprForAggregateCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForAggregateCompare(elem);
  for (auto* arg : expr->args) WalkExprForAggregateCompare(arg);
}

void ElaboratorOperationRules::WalkStmtsForAggregateCompare(const Stmt* s) {
  if (!s) return;
  WalkExprForAggregateCompare(s->rhs);
  WalkExprForAggregateCompare(s->lhs);
  WalkExprForAggregateCompare(s->expr);
  WalkExprForAggregateCompare(s->condition);
  WalkExprForAggregateCompare(s->assert_expr);
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForAggregateCompare(sub); });
}

void ElaboratorOperationRules::ValidateAggregateComparisons(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForAggregateCompare(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAggregateCompare(item->assign_rhs);
    }
  }
}

void ElaboratorOperationRules::CheckTypeRefCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  bool lhs_is_type = expr->lhs->kind == ExprKind::kTypeRef;
  bool rhs_is_type = expr->rhs->kind == ExprKind::kTypeRef;
  if (lhs_is_type == rhs_is_type) return;
  diag_.Error(expr->range.start,
              "type reference may be compared only with another type "
              "reference",
              Subclause("6.23"));
}

static bool IsTypeRef(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kTypeRef;
}

void ElaboratorOperationRules::ReportTypeRefOperand(const Expr* operand,
                                                    const Expr* op) {
  if (operand->kind != ExprKind::kTypeRef) return;
  diag_.Error(op->range.start,
              "a type reference may only be used with the equality, "
              "inequality, and case equality/inequality operators",
              Subclause("6.23"));
}

void ElaboratorOperationRules::WalkExprForTypeRefCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kUnary) ReportTypeRefOperand(expr->lhs, expr);
  if (expr->kind == ExprKind::kTernary) {
    ReportTypeRefOperand(expr->condition, expr);
    ReportTypeRefOperand(expr->true_expr, expr);
    ReportTypeRefOperand(expr->false_expr, expr);
  }
  if (expr->kind == ExprKind::kInside) {
    const auto kItem = std::ranges::find_if(expr->elements, IsTypeRef);
    ReportTypeRefOperand(kItem == expr->elements.end() ? expr->lhs : *kItem,
                         expr);
  }
  if (expr->kind == ExprKind::kBinary) {
    bool is_equality =
        expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq ||
        expr->op == TokenKind::kEqEqEq || expr->op == TokenKind::kBangEqEq;
    if (is_equality) {
      CheckTypeRefCompareOp(expr);
    } else if (IsTypeRef(expr->lhs) || IsTypeRef(expr->rhs)) {
      diag_.Error(expr->range.start,
                  "a type reference may only be used with the equality, "
                  "inequality, and case equality/inequality operators",
                  Subclause("6.23"));
    }
  }
  WalkExprForTypeRefCompare(expr->lhs);
  WalkExprForTypeRefCompare(expr->rhs);
  WalkExprForTypeRefCompare(expr->condition);
  WalkExprForTypeRefCompare(expr->true_expr);
  WalkExprForTypeRefCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForTypeRefCompare(elem);
  for (auto* arg : expr->args) WalkExprForTypeRefCompare(arg);
}

void ElaboratorOperationRules::WalkStmtsForTypeRefCompare(const Stmt* s) {
  if (!s) return;
  ForEachChildExpr(s, [this](const Expr* e) { WalkExprForTypeRefCompare(e); });
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForTypeRefCompare(sub); });
}

void ElaboratorOperationRules::ValidateTypeRefComparisons(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForTypeRefCompare(item->body);
    }
    for (const Stmt* s : item->func_body_stmts) WalkStmtsForTypeRefCompare(s);
    WalkExprForTypeRefCompare(item->init_expr);
    WalkExprForTypeRefCompare(item->assign_rhs);
  }
}

static const Expr* MemberChainRoot(const Expr* e) {
  while (true) {
    if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      e = e->lhs;
    } else if (e->kind == ExprKind::kSelect && e->base != nullptr) {
      e = e->base;
    } else {
      return e;
    }
  }
}

bool ElaboratorOperationRules::IsHierarchicalMemberAccess(const Expr* e) const {
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution)
    return false;
  return !NamesSelectableValue(MemberChainRoot(e->lhs));
}

static bool EnumeratesConstant(const DataType& type, std::string_view name) {
  return type.kind == DataTypeKind::kEnum &&
         std::ranges::any_of(type.enum_members, [&](const EnumMember& m) {
           return m.name == name;
         });
}

static bool DeclaresTypeParameter(const ModuleItem& item) {
  return item.data_type.kind == DataTypeKind::kVoid &&
         item.typedef_type.kind != DataTypeKind::kImplicit;
}

bool ElaboratorOperationRules::DeclaresSelectableType(const DataType& type) {
  return type.kind != DataTypeKind::kVirtualInterface;
}

bool ElaboratorOperationRules::DeclaresSelectableValue(
    const std::vector<ModuleItem*>& items, std::string_view name) const {
  return std::ranges::any_of(items, [&](const ModuleItem* item) {
    if (item == nullptr) return false;
    if (EnumeratesConstant(item->data_type, name) ||
        EnumeratesConstant(item->typedef_type, name)) {
      return true;
    }
    if (item->name != name) return false;
    switch (item->kind) {
      case ModuleItemKind::kVarDecl:
      case ModuleItemKind::kNetDecl:
        return DeclaresSelectableType(item->data_type);
      case ModuleItemKind::kParamDecl:
        return !DeclaresTypeParameter(*item);
      default:
        return false;
    }
  });
}

bool ElaboratorOperationRules::ImportsSelectableValue(
    const std::vector<ModuleItem*>& items, std::string_view name) const {
  return std::ranges::any_of(items, [&](const ModuleItem* item) {
    if (item == nullptr || item->kind != ModuleItemKind::kImportDecl)
      return false;
    const ImportItem& import = item->import_item;
    if (!import.is_wildcard && import.item_name != name) return false;
    const PackageDecl* pkg = PackageNamed(*unit_, import.package_name);
    return pkg != nullptr && DeclaresSelectableValue(pkg->items, name);
  });
}

static bool DeclaresDataPort(const ModuleDecl& decl, std::string_view name) {
  return std::ranges::any_of(decl.ports, [&](const PortDecl& port) {
    return port.name == name && !port.is_interface_port &&
           !port.is_explicit_named && port.port_expr == nullptr;
  });
}

const ModuleDecl* ElaboratorOperationRules::TypeRefModule() const {
  if (type_ref_module_ != nullptr) return type_ref_module_;
  return module_decl_path_.empty() ? nullptr : module_decl_path_.back();
}

bool ElaboratorOperationRules::NamesModuleValue(std::string_view name) const {
  auto var = var_types_.find(name);
  if (var != var_types_.end()) {
    return var->second != DataTypeKind::kVirtualInterface;
  }
  if (const_names_.contains(name) || enum_member_names_.contains(name))
    return true;
  if (type_ref_package_ != nullptr &&
      (DeclaresSelectableValue(type_ref_package_->items, name) ||
       ImportsSelectableValue(type_ref_package_->items, name))) {
    return true;
  }
  const ModuleDecl* decl = TypeRefModule();
  if (decl != nullptr && (DeclaresDataPort(*decl, name) ||
                          DeclaresSelectableValue(decl->items, name) ||
                          ImportsSelectableValue(decl->items, name))) {
    return true;
  }
  return ImportsSelectableValue(unit_->cu_items, name) ||
         DeclaresSelectableValue(unit_->cu_items, name);
}

bool ElaboratorOperationRules::NamesSelectableValue(const Expr* root) const {
  if (root->kind == ExprKind::kMemberAccess) {
    const PackageDecl* pkg = PackageNamed(*unit_, root->lhs->text);
    return pkg != nullptr &&
           DeclaresSelectableValue(pkg->items, root->rhs->text);
  }
  if (root->kind != ExprKind::kIdentifier) return true;
  if (root->text == "this" || root->text == "super") return true;
  if (root->scope_prefix == "$root") return false;
  if (root->scope_prefix == "$unit")
    return DeclaresSelectableValue(unit_->cu_items, root->text);
  if (const BlockValue* local = InnermostBlockValue(root->text))
    return local->selectable;
  return NamesModuleValue(root->text);
}

TypeRefResolver ElaboratorOperationRules::ResolverAmongLocals(
    const RtlirModule* mod, std::function<void(DataType&, SourceLoc)> resolve) {
  return [this, mod, resolve = std::move(resolve)](
             DataType& dt, SourceLoc loc,
             std::span<const ProceduralLocal> locals) {
    std::vector<Expr*> taken;
    InLocals(locals, [&] {
      taken = TypeRefUnpackedDims(dt.type_ref_expr, mod);
      resolve(dt, loc);
    });
    return taken;
  };
}

bool ElaboratorOperationRules::TypeRefArgHasMemberAccess(const Expr* e) const {
  if (!e) return false;
  if (IsHierarchicalMemberAccess(e)) return true;
  if (TypeRefArgHasMemberAccess(e->lhs)) return true;
  if (TypeRefArgHasMemberAccess(e->rhs)) return true;
  if (TypeRefArgHasMemberAccess(e->base)) return true;
  if (TypeRefArgHasMemberAccess(e->index)) return true;
  if (TypeRefArgHasMemberAccess(e->condition)) return true;
  if (TypeRefArgHasMemberAccess(e->true_expr)) return true;
  if (TypeRefArgHasMemberAccess(e->false_expr)) return true;
  for (const auto* elem : e->elements) {
    if (TypeRefArgHasMemberAccess(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (TypeRefArgHasMemberAccess(arg)) return true;
  }
  return false;
}

bool ElaboratorOperationRules::TypeRefArgUsesDynamicElement(
    const Expr* e, const RtlirModule* mod) const {
  if (e == nullptr) return false;
  bool selects = false;
  auto judge = [&](const ExprTypeScope& scope) {
    selects = SelectsDynamicElement(e, scope);
  };
  if (mod != nullptr) {
    InExprTypeScope(*mod, judge);
  } else {
    InUnitExprTypeScope(judge);
  }
  return selects;
}

void ElaboratorOperationRules::ReportDynamicElementArg(const Expr* inner,
                                                       SourceLoc loc,
                                                       const RtlirModule* mod) {
  if (reported_type_ref_args_.contains(inner) ||
      !TypeRefArgUsesDynamicElement(inner, mod)) {
    return;
  }
  reported_type_ref_args_.insert(inner);
  diag_.Error(loc,
              "type operator argument shall not reference elements of "
              "dynamic objects",
              Subclause("6.23"));
}

bool ElaboratorOperationRules::ReportHierarchicalArg(const Expr* inner,
                                                     SourceLoc loc) {
  if (!inner || reported_type_ref_args_.contains(inner)) return true;
  if (!TypeRefArgHasMemberAccess(inner)) return false;
  reported_type_ref_args_.insert(inner);
  diag_.Error(loc,
              "type operator argument uses a hierarchical reference, which "
              "the type operator does not accept",
              Subclause("6.23"));
  return true;
}

void ElaboratorOperationRules::CheckTypeRefArgInner(const Expr* inner,
                                                    SourceLoc loc,
                                                    const RtlirModule* mod) {
  if (!ReportHierarchicalArg(inner, loc)) {
    ReportDynamicElementArg(inner, loc, mod);
  }
}

void ElaboratorOperationRules::CheckDynamicElementArgsOfStmt(
    const Stmt* s, const RtlirModule* mod) {
  ForEachTypeRefOfStmt(s, [&](const Expr* ref) {
    ReportDynamicElementArg(ref->lhs, ref->range.start, mod);
  });
}

void ElaboratorOperationRules::WalkExprForTypeRefArg(const Expr* expr) {
  ForEachTypeRef(expr, [this](const Expr* ref) {
    CheckTypeRefArgInner(ref->lhs, ref->range.start, type_ref_mod_);
  });
}

void ElaboratorOperationRules::WalkStmtsForTypeRefArg(const Stmt* s) {
  if (!s) return;
  ForEachTypeRefOfStmt(s, [this](const Expr* ref) {
    ReportHierarchicalArg(ref->lhs, ref->range.start);
  });
  ReportHierarchicalArg(s->var_decl_type.type_ref_expr, s->range.start);
  size_t mark = type_ref_block_vars_.size();
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForTypeRefArg(sub); });
  type_ref_block_vars_.resize(mark);
  if (s->kind == StmtKind::kVarDecl) {
    type_ref_block_vars_.push_back({s->var_name,
                                    DeclaresSelectableType(s->var_decl_type),
                                    &s->var_decl_type, &s->var_unpacked_dims});
  }
}

void ElaboratorOperationRules::WalkItemExprsForTypeRefArg(
    const ModuleItem* item) {
  ForEachItemExprTypeRef(item, [this](const Expr* operand, SourceLoc loc) {
    CheckTypeRefArgInner(operand, loc, type_ref_mod_);
  });
}

void ElaboratorOperationRules::ValidateTypeRefArgs(const ModuleDecl* decl) {
  type_ref_module_ = decl;
  for (const auto& param : decl->params) WalkExprForTypeRefArg(param.second);
  for (const auto* item : decl->items) {
    if (item->data_type.type_ref_expr) {
      CheckTypeRefArgInner(item->data_type.type_ref_expr, item->loc,
                           type_ref_mod_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForTypeRefArg(item->body);
    }
    WalkItemExprsForTypeRefArg(item);
  }
  type_ref_module_ = nullptr;
}

static bool IsIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:

    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:

    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:

    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:

    case TokenKind::kPercent:

    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

static bool IsUnaryIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

void ElaboratorOperationRules::WalkExprForRealOps(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary) {
    bool lhs_real = expr->lhs && IsRealValued(expr->lhs, var_types_);
    bool rhs_real = expr->rhs && IsRealValued(expr->rhs, var_types_);
    if ((lhs_real || rhs_real) && IsIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  std::format("binary operator {} is not allowed on real "
                              "operands",
                              TokenKindName(expr->op)),
                  Subclause("11.3.1"));
    }
  }
  if (expr->kind == ExprKind::kUnary) {
    bool operand_real = expr->lhs && IsRealValued(expr->lhs, var_types_);
    if (operand_real && IsUnaryIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  std::format("unary operator {} is not allowed on real "
                              "operands",
                              TokenKindName(expr->op)),
                  Subclause("11.3.1"));
    }
  }
  WalkExprForRealOps(expr->lhs);
  WalkExprForRealOps(expr->rhs);
  WalkExprForRealOps(expr->condition);
  WalkExprForRealOps(expr->true_expr);
  WalkExprForRealOps(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForRealOps(elem);
  for (auto* arg : expr->args) WalkExprForRealOps(arg);
}

void ElaboratorOperationRules::WalkStmtsForRealOps(const Stmt* s) {
  if (!s) return;
  WalkExprForRealOps(s->rhs);
  WalkExprForRealOps(s->lhs);
  WalkExprForRealOps(s->expr);
  WalkExprForRealOps(s->condition);
  WalkExprForRealOps(s->assert_expr);
  WalkExprForRealOps(s->var_init);
  ForEachChildStmt(s, [this](Stmt* const& sub) { WalkStmtsForRealOps(sub); });
}

void ElaboratorOperationRules::WalkSubroutineForRealOps(
    const ModuleItem* item) {
  if (item->func_args.empty()) {
    for (const Stmt* s : item->func_body_stmts) WalkStmtsForRealOps(s);
    return;
  }
  auto module_types = var_types_;
  for (const auto& arg : item->func_args)
    var_types_[arg.name] = arg.data_type.kind;
  for (const Stmt* s : item->func_body_stmts) WalkStmtsForRealOps(s);
  var_types_ = std::move(module_types);
}

void ElaboratorOperationRules::WalkItemsForRealOps(
    const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (IsProceduralItemKind(item->kind)) WalkStmtsForRealOps(item->body);
    if (item->kind == ModuleItemKind::kContAssign)
      WalkExprForRealOps(item->assign_rhs);
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl)
      WalkExprForRealOps(item->init_expr);
    WalkSubroutineForRealOps(item);
    WalkItemsForRealOps(item->gen_body);
    if (item->gen_else != nullptr) WalkItemsForRealOps({item->gen_else});
    for (const auto& case_item : item->gen_case_items)
      WalkItemsForRealOps(case_item.body);
  }
}

void ElaboratorOperationRules::ValidateRealOperatorRestrictions(
    const ModuleDecl* decl) {
  WalkItemsForRealOps(decl->items);
}

namespace {

bool IsSizeCastForm(const Expr* cast) {
  return cast->text.empty() && cast->rhs != nullptr && cast->lhs != nullptr &&
         cast->lhs->kind != ExprKind::kAssignmentPattern &&
         cast->rhs->kind != ExprKind::kTypeRef;
}

bool IsSigningCast(const Expr* cast) {
  return cast->text == "signed" || cast->text == "unsigned";
}

bool IsSigningSystemCall(const Expr* call) {
  return call->kind == ExprKind::kSystemCall &&
         (call->callee == "$signed" || call->callee == "$unsigned");
}

}  // namespace

bool ElaboratorOperationRules::CastOperandIsReal(const Expr* operand) const {
  return operand != nullptr && IsRealValued(operand, var_types_);
}

void ElaboratorOperationRules::CheckSigningSystemCallExpr(const Expr* expr) {
  if (!expr || !IsSigningSystemCall(expr) || expr->args.empty()) return;
  if (!CastOperandIsReal(expr->args.front())) return;
  diag_.Error(expr->range.start,
              std::format("{} works only on an integral value", expr->callee),
              Subclause("11.7"));
}

void ElaboratorOperationRules::CheckCastExpr(const Expr* expr) {
  CheckSigningSystemCallExpr(expr);
  if (!expr || expr->kind != ExprKind::kCast) return;

  if (IsSizeCastForm(expr)) {
    auto size = ConstEvalInt(expr->rhs);
    if (size) {
      if (*size <= 0) {
        diag_.Error(expr->range.start,
                    "size cast target width must be a positive constant",
                    Subclause("6.24.1"));
      } else if (CastOperandIsNonIntegral(expr->lhs)) {
        diag_.Error(expr->range.start,
                    "a size cast works only on an integral value",
                    Subclause("6.24.1"));
      }
    }
  } else if (IsSigningCast(expr) && CastOperandIsNonIntegral(expr->lhs)) {
    diag_.Error(expr->range.start,
                "a signing cast works only on an integral value",
                Subclause("6.24.1"));
  }
}

}  // namespace delta
