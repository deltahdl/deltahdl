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
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
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

// Two whole unpacked-array operands compare legally only when their element
// type and dimension sizes match (§6.22.2). A typedef array's dimensions are
// not recorded on the variable, so use the typedef's cached fixed unpacked
// width as the shape key: differing widths are necessarily non-equivalent.
// Returns true when both operands are unpacked-array typedef variables, i.e.
// the comparison was fully handled here.
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

// §6.22.2 with §7.4.6: whether the operands of the comparison `expr` are two
// unpacked arrays whose shapes ArrayOperandsEquivalent knows, reporting them
// where they are not equivalent.
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
  // §11.4.11 with §6.22.2: a conditional's two array operands are of
  // equivalent types or the conditional is illegal, as an equality's are.
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
  // §6.22.2 makes a comparison of two non-equivalent aggregate operands illegal
  // and names no statement the rule is suspended in, so this descends every
  // link ForEachChildStmt in elaborator_validate_internal.h names. It wrote out
  // six of the thirteen, so a comparison of two differently typed structures
  // written as a fork arm, as a randcase item or in a randsequence production
  // reached CheckAggregateCompareOp through nothing and elaborated clean.
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

// §6.23 — A type reference used in an equality, inequality, case-equality,
// or case-inequality comparison shall only be compared with another type
// reference. Reject any such comparison whose other operand is a value
// expression rather than a kTypeRef node.
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

// A.10 footnote 45 with §11.11 Syntax 11-7: a type_reference primary takes
// none of the unary operators, no part of a conditional, whose predicate and
// branches are operands as a binary operator's are, and no part of §11.4.13's
// set membership operator. Those operands are always written, so none is null
// here.
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
  // `inside` is reported once, at the first type reference among the items of
  // its range list, or else at its left operand where that is one.
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
      // §A.10: a type_reference primary is restricted to the equality,
      // inequality, case-equality, and case-inequality operators (and to use
      // as the casting type of a static cast, which is not a binary operator).
      // Any other operator applied to a type_reference is illegal.
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
  // §6.23 admits a type reference in a comparison only against another type
  // reference, and A.10 restricts it to the four equality operators, neither
  // conditioned on the statement the comparison stands in, so this reads
  // every expression of a statement ForEachChildExpr names and descends every
  // link ForEachChildStmt names, both in elaborator_validate_internal.h. It
  // wrote out six of the thirteen links, so `type(T) == 5` written as a fork
  // arm or as an immediate assertion's else action was never compared at all,
  // and five of the expressions, so a block variable's initializer was not.
  ForEachChildExpr(s, [this](const Expr* e) { WalkExprForTypeRefCompare(e); });
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForTypeRefCompare(sub); });
}

void ElaboratorOperationRules::ValidateTypeRefComparisons(
    const ModuleDecl* decl) {
  // The rules hold wherever a type reference stands: in a procedural block or
  // a subroutine body, a continuous assignment, and a declaration's or a
  // parameter's initializer.
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

// What a chain of `.` accesses and selects starts from: `a` of `a[1].b.c[2]`,
// a `p::v` scope resolution, or the call or other expression the chain is
// written on.
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

// §6.23 — the expression supplied to the type operator shall not contain a
// hierarchical reference or a reference to an element of a dynamic object.
// A member-access subtree written with `.` is treated as a hierarchical
// reference, but for the two kinds of access below; a select whose base names
// a dynamic array or associative array is treated as a reference to a
// dynamic-object element.
//
// §8.23 names the type operator as one of the contexts in which an incomplete
// forward type, a type defined by an interface-based typedef, or a type
// parameter may prefix the class scope resolution operator `::`, so a
// kMemberAccess node whose Expr::is_scope_resolution is true is not by itself a
// hierarchical reference. §6.20.3 draws the same distinction for a data type
// parameter: package references are permitted and hierarchical names are not.
// The descent into the children of a `::` node still runs, so `type(C::x.y)`
// and any `::` node holding a `.` node below it remain errors.
//
// §7.2 with §6.23 and §23.6: nor is a `.` that selects a member of a value or
// calls a built-in method of one, `p.f` of a structure `p` or `s.len()` of a
// string `s`, which names no scope (NamesSelectableValue). The value is what
// the chain of `.` accesses and selects the access ends is written on.
bool ElaboratorOperationRules::IsHierarchicalMemberAccess(const Expr* e) const {
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution)
    return false;
  return !NamesSelectableValue(MemberChainRoot(e->lhs));
}

// The package `unit` declares as `name`; null where it declares none.
static const PackageDecl* PackageNamed(const CompilationUnit& unit,
                                       std::string_view name) {
  auto it = std::ranges::find_if(unit.packages, [&](const PackageDecl* p) {
    return p != nullptr && p->name == name;
  });
  return it != unit.packages.end() ? *it : nullptr;
}

// Whether `type` is an enumeration one of whose named constants is `name`
// (§6.19).
static bool EnumeratesConstant(const DataType& type, std::string_view name) {
  return type.kind == DataTypeKind::kEnum &&
         std::ranges::any_of(type.enum_members, [&](const EnumMember& m) {
           return m.name == name;
         });
}

// §6.20.3: whether the parameter `item` declares is a type parameter.
static bool DeclaresTypeParameter(const ModuleItem& item) {
  return item.data_type.kind == DataTypeKind::kVoid &&
         item.typedef_type.kind != DataTypeKind::kImplicit;
}

// Whether a variable declared with `type` has members a `.` selects: any but
// a virtual interface, which stands for an instance. A class handle's `.`
// selects a property or a method of the class (§8.5, §8.6), a member of the
// object rather than an element of it.
bool ElaboratorOperationRules::DeclaresSelectableType(const DataType& type) {
  return type.kind != DataTypeKind::kVirtualInterface;
}

// Whether `items`, a package's or the compilation unit's declarations,
// declare `name` as a value whose members a `.` selects: a variable or net of
// a type DeclaresSelectableType accepts, a value parameter, or a named
// constant of an enumeration a typedef or a declaration writes.
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

// §26.3: whether one of the imports among `items` makes `name` a value whose
// members a `.` selects: an import of the name itself, or a wildcard import of
// a package declaring it.
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

// §23.2.2: whether `decl` has a port the body knows as `name` that carries a
// value: one an interface port (§25.5), which stands for an instance, and one
// whose name is external alone (§23.2.2.1) are not.
static bool DeclaresDataPort(const ModuleDecl& decl, std::string_view name) {
  return std::ranges::any_of(decl.ports, [&](const PortDecl& port) {
    return port.name == name && !port.is_interface_port &&
           !port.is_explicit_named && port.port_expr == nullptr;
  });
}

// The module whose type references CheckTypeRefArgInner judges: the one
// ValidateTypeRefArgs walks, or else the one being elaborated.
const ModuleDecl* ElaboratorOperationRules::TypeRefModule() const {
  if (type_ref_module_ != nullptr) return type_ref_module_;
  return module_decl_path_.empty() ? nullptr : module_decl_path_.back();
}

// Whether the bare `name` names a value of the module whose members a `.`
// selects: a variable or net it declares, a parameter, an enumeration's named
// constant, a port carrying a value, or a value an import of the module or of
// the compilation unit takes, or the unit declares (§3.12.1).
bool ElaboratorOperationRules::NamesModuleValue(std::string_view name) const {
  auto var = var_types_.find(name);
  if (var != var_types_.end()) {
    return var->second != DataTypeKind::kVirtualInterface &&
           class_var_names_.count(name) == 0;
  }
  if (const_names_.contains(name) || enum_member_names_.contains(name))
    return true;
  const ModuleDecl* decl = TypeRefModule();
  if (decl != nullptr && (DeclaresDataPort(*decl, name) ||
                          DeclaresSelectableValue(decl->items, name) ||
                          ImportsSelectableValue(decl->items, name))) {
    return true;
  }
  return ImportsSelectableValue(unit_->cu_items, name) ||
         DeclaresSelectableValue(unit_->cu_items, name);
}

// Whether `root`, what a chain of `.` accesses and selects starts from, names
// a value whose members a `.` selects, rather than a scope (§23.6): the value
// of a call or of any expression but a name; a value a package declares,
// written behind `::` (§26.3), or the compilation unit, behind `$unit::`
// (§3.12.1); a variable a block around the type operator declares, the
// innermost declaration of the name deciding; or a value of the module
// (NamesModuleValue). A name `$root.` heads names a top-level instance.
bool ElaboratorOperationRules::NamesSelectableValue(const Expr* root) const {
  if (root->kind == ExprKind::kMemberAccess) {
    const PackageDecl* pkg = PackageNamed(*unit_, root->lhs->text);
    return pkg != nullptr &&
           DeclaresSelectableValue(pkg->items, root->rhs->text);
  }
  if (root->kind != ExprKind::kIdentifier) return true;
  if (root->scope_prefix == "$root") return false;
  if (root->scope_prefix == "$unit")
    return DeclaresSelectableValue(unit_->cu_items, root->text);
  for (auto decl = type_ref_block_vars_.rbegin();
       decl != type_ref_block_vars_.rend(); ++decl) {
    if (decl->first == root->text) return decl->second;
  }
  return NamesModuleValue(root->text);
}

TypeRefResolver ElaboratorOperationRules::ResolverAmongLocals(
    const RtlirModule* mod, std::function<void(DataType&, SourceLoc)> resolve) {
  return [this, mod, resolve = std::move(resolve)](
             DataType& dt, SourceLoc loc,
             std::span<const ProceduralLocal> locals) {
    const size_t kMark = type_ref_block_vars_.size();
    for (const ProceduralLocal& local : locals) {
      type_ref_block_vars_.emplace_back(local.name,
                                        DeclaresSelectableType(*local.type));
    }
    std::vector<Expr*> taken = TypeRefUnpackedDims(dt.type_ref_expr, mod);
    resolve(dt, loc);
    type_ref_block_vars_.resize(kMark);
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

// True when this node is itself a select on a dynamic object; the recursive
// descent into children is handled separately by the caller. Dynamic arrays,
// queues, and associative arrays are all variable-size (dynamic) objects, so a
// select into any of them is a reference to an element of a dynamic object.
static bool TypeRefArgSelectsDynamicElement(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        array_info) {
  if (e->kind != ExprKind::kSelect || !e->base ||
      e->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto it = array_info.find(e->base->text);
  return it != array_info.end() &&
         (it->second.is_dynamic || it->second.is_assoc || it->second.is_queue);
}

bool ElaboratorOperationRules::TypeRefArgUsesDynamicElement(
    const Expr* e) const {
  if (!e) return false;
  if (TypeRefArgSelectsDynamicElement(e, var_array_info_)) return true;
  const Expr* const kChildren[] = {e->lhs,       e->rhs,       e->base,
                                   e->index,     e->condition, e->true_expr,
                                   e->false_expr};
  for (const Expr* child : kChildren) {
    if (TypeRefArgUsesDynamicElement(child)) return true;
  }
  for (const auto* elem : e->elements) {
    if (TypeRefArgUsesDynamicElement(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (TypeRefArgUsesDynamicElement(arg)) return true;
  }
  return false;
}

void ElaboratorOperationRules::CheckTypeRefArgInner(const Expr* inner,
                                                    SourceLoc loc) {
  if (!inner) return;
  if (TypeRefArgHasMemberAccess(inner)) {
    diag_.Error(loc,
                "type operator argument uses a hierarchical reference, which "
                "the type operator does not accept",
                Subclause("6.23"));
    return;
  }
  if (TypeRefArgUsesDynamicElement(inner)) {
    diag_.Error(loc,
                "type operator argument shall not reference elements of "
                "dynamic objects",
                Subclause("6.23"));
  }
}

void ElaboratorOperationRules::WalkExprForTypeRefArg(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kTypeRef) {
    CheckTypeRefArgInner(expr->lhs, expr->range.start);
  }
  WalkExprForTypeRefArg(expr->lhs);
  WalkExprForTypeRefArg(expr->rhs);
  WalkExprForTypeRefArg(expr->condition);
  WalkExprForTypeRefArg(expr->true_expr);
  WalkExprForTypeRefArg(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForTypeRefArg(elem);
  for (auto* arg : expr->args) WalkExprForTypeRefArg(arg);
}

void ElaboratorOperationRules::WalkStmtsForTypeRefArg(const Stmt* s) {
  if (!s) return;
  WalkExprForTypeRefArg(s->lhs);
  WalkExprForTypeRefArg(s->rhs);
  WalkExprForTypeRefArg(s->expr);
  WalkExprForTypeRefArg(s->condition);
  WalkExprForTypeRefArg(s->assert_expr);
  if (s->var_decl_type.type_ref_expr) {
    CheckTypeRefArgInner(s->var_decl_type.type_ref_expr, s->range.start);
  }
  // §6.23 bars a hierarchical reference and a reference to an element of a
  // dynamic object from the operand of the type operator wherever the operator
  // is written, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names. It wrote out six of the thirteen, so
  // `type(d[0])` on a dynamic array `d` went unreported in a fork arm and in a
  // for-loop step.
  //
  // §6.21 with §7.2: a variable a block declares is in scope for the rest of
  // the block, where a `.` after it selects a member as after a module's; the
  // declarations a statement's children make are forgotten when it is left,
  // and a declaration is recorded after its own initializer is checked.
  size_t mark = type_ref_block_vars_.size();
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForTypeRefArg(sub); });
  type_ref_block_vars_.resize(mark);
  if (s->kind == StmtKind::kVarDecl) {
    type_ref_block_vars_.emplace_back(s->var_name,
                                      DeclaresSelectableType(s->var_decl_type));
  }
}

// The expressions `item` writes outside any statement: a continuous
// assignment's right-hand side, a parameter's value (§6.20.2) and the ranges of
// a net or variable declaration (§11.2.1), the last two of which leave the
// operand of a type reference in them to this rule (ExprContainsHierRef).
void ElaboratorOperationRules::WalkItemExprsForTypeRefArg(
    const ModuleItem* item) {
  if (item->kind == ModuleItemKind::kContAssign) {
    WalkExprForTypeRefArg(item->assign_rhs);
  }
  if (item->kind == ModuleItemKind::kParamDecl) {
    WalkExprForTypeRefArg(item->init_expr);
  }
  if (item->kind != ModuleItemKind::kNetDecl &&
      item->kind != ModuleItemKind::kVarDecl) {
    return;
  }
  WalkExprForTypeRefArg(item->data_type.packed_dim_left);
  WalkExprForTypeRefArg(item->data_type.packed_dim_right);
  for (const auto& [left, right] : item->data_type.extra_packed_dims) {
    WalkExprForTypeRefArg(left);
    WalkExprForTypeRefArg(right);
  }
  for (const Expr* dim : item->unpacked_dims) WalkExprForTypeRefArg(dim);
}

void ElaboratorOperationRules::ValidateTypeRefArgs(const ModuleDecl* decl) {
  type_ref_module_ = decl;
  // The values of the parameters the header's parameter port list declares.
  for (const auto& param : decl->params) WalkExprForTypeRefArg(param.second);
  for (const auto* item : decl->items) {
    if (item->data_type.type_ref_expr) {
      CheckTypeRefArgInner(item->data_type.type_ref_expr, item->loc);
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

    // §11.3's Table 11-1 gives the assignment operators the operand types of
    // the operators they are formed from, so only =, +=, -=, *= and /= admit a
    // real operand.
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
      // §11.3.1 states its rule as Table 11-1, which admits or bars each
      // operator separately, so the report names the operator it barred.
      // TokenKindName in src/lexer/keywords.cpp answers with the source
      // spelling the table lists, already quoted.
      //
      // The form is named too, because `&`, `|`, `^`, `~^` and `^~` are each
      // both a binary and a unary operator, and the spelling alone leaves the
      // reader to work out which reading the elaborator took.
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
  // §11.3.1's Table 11-1 decides which operators a real operand admits and
  // names no statement the table is suspended in, so this descends every link
  // ForEachChildStmt in elaborator_validate_internal.h names. It wrote out six
  // of the thirteen, so `c = a & b;` on real `a` and `b` was reported in a
  // begin-end block and accepted in a fork arm or a for-loop step.
  ForEachChildStmt(s, [this](Stmt* const& sub) { WalkStmtsForRealOps(sub); });
}

// A subroutine's statements, its formals entered under their declared kinds
// while they are walked, each hiding a module variable of its name, so that
// `return a % 2;` on a real formal `a` is judged as on a real variable.
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

// §11.3.1 names no place its operand rules are suspended in, so they are held
// in every one the module writes an expression in: a process's statements, a
// continuous assignment, a declaration's initializer, a subroutine's
// statements, and each of these in the blocks of a generate construct.
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

// §6.24.1: a numeric size cast writes its target width as a constant_primary --
// an integer literal, a constant parameter, or a constant expression -- rather
// than a named type. The parser records these in the "node cast" form: the
// width expression is carried in rhs and the value being cast in lhs, leaving
// the type-name text empty. A cast that names a type (int', signed', or a
// user-defined type) sets the text field, and a cast whose operand is an
// assignment pattern (type'{...}) or whose casting type is a type reference is
// not a size cast either. Membership here is provisional: only a rhs that
// actually evaluates to a constant integer is treated as a size.
bool IsSizeCastForm(const Expr* cast) {
  return cast->text.empty() && cast->rhs != nullptr && cast->lhs != nullptr &&
         cast->lhs->kind != ExprKind::kAssignmentPattern &&
         cast->rhs->kind != ExprKind::kTypeRef;
}

// §6.24.1: signed'() and unsigned'() change only the signedness of the operand.
bool IsSigningCast(const Expr* cast) {
  return cast->text == "signed" || cast->text == "unsigned";
}

// §11.7: $signed() and $unsigned() are the system-function spelling of the same
// signedness change the signing cast writes, and the parser records a call to
// either one as a kSystemCall whose callee carries the leading '$'.
bool IsSigningSystemCall(const Expr* call) {
  return call->kind == ExprKind::kSystemCall &&
         (call->callee == "$signed" || call->callee == "$unsigned");
}

}  // namespace

// §6.24.1: a real value has no bit representation of its own, so the two casts
// that reinterpret an operand as a packed vector -- the size cast and the
// signing cast -- require an integral operand. A real variable or a real
// literal used directly as such an operand is rejected here at elaboration.
//
// A time literal is one of those real operands. §5.8 interprets it as a
// realtime value scaled to the current time unit, so 2.1ns is a real value and
// not a value of the type named time, which §6.11 defines as a 64-bit integral
// type. That reading is what this test used to have, admitting kRealLiteral
// alone and letting signed'(2.1ns), 8'(2.1ns) and $signed(2.1ns) through while
// the same conversions applied to a realtime variable were rejected.
bool ElaboratorOperationRules::CastOperandIsReal(const Expr* operand) const {
  return operand != nullptr && IsRealValued(operand, var_types_);
}

// §11.7: $signed and $unsigned shall return a one-dimensional packed array with
// the same number of bits and value as the input expression, so the input has
// to have bits to return and a real argument has none. The argument is rejected
// here by CastOperandIsReal, the same test the signing cast uses, which states
// above it which operands count as real.
//
// This spelling cites §11.7 and the cast spelling cites §6.24.1 because each
// clause states the requirement for the syntax it defines; §11.7 is what makes
// the two one conversion, defining these functions in terms of the signedness
// the cast applies. Left unreported, the argument reaches EvalSignCast in
// src/simulator/eval_systask.cpp, which sets is_signed on the real value it
// evaluated, and the result claims to be both a real and a signed integer.
void ElaboratorOperationRules::CheckSigningSystemCallExpr(const Expr* expr) {
  if (!expr || !IsSigningSystemCall(expr) || expr->args.empty()) return;
  if (!CastOperandIsReal(expr->args.front())) return;
  diag_.Error(expr->range.start,
              std::format("{} works only on an integral value", expr->callee),
              Subclause("11.7"));
}

void ElaboratorOperationRules::CheckCastExpr(const Expr* expr) {
  // §11.7's system-function spelling of the signing conversion is checked from
  // here because WalkExprForCast in
  // src/elaborator/elaborator_validate_cast_ops.cpp visits every expression and
  // calls only this member, and the early return below drops every node that is
  // not a cast.
  CheckSigningSystemCallExpr(expr);
  if (!expr || expr->kind != ExprKind::kCast) return;

  if (IsSizeCastForm(expr)) {
    // A confirmed numeric size cast: the casting type evaluates to a constant
    // integer. If it does not evaluate here, the rhs may name a type or an
    // unresolved parameter, so no size rule is applied.
    auto size = ConstEvalInt(expr->rhs);
    if (size) {
      // §6.24.1: a size written as a constant expression has to come out
      // positive, so zero or a negative size is an error.
      if (*size <= 0) {
        diag_.Error(expr->range.start,
                    "size cast target width must be a positive constant",
                    Subclause("6.24.1"));
      } else if (CastOperandIsNonIntegral(expr->lhs)) {
        // §6.24.1: a size cast takes an integral operand only.
        diag_.Error(expr->range.start,
                    "a size cast works only on an integral value",
                    Subclause("6.24.1"));
      }
    }
  } else if (IsSigningCast(expr) && CastOperandIsNonIntegral(expr->lhs)) {
    // §6.24.1: a signing cast takes an integral operand only.
    diag_.Error(expr->range.start,
                "a signing cast works only on an integral value",
                Subclause("6.24.1"));
  }
}

}  // namespace delta
