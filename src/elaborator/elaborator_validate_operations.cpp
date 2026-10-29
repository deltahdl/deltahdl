#include "elaborator/elaborator_validate_operations.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_or_variable_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

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

// §6.23 — a type_reference used in a comparison denotes a data type. Its inner
// operand parses either as a data type (a built-in keyword, kept in `text`) or,
// for a user name, as an identifier expression (kept in `lhs`). Map that to the
// concrete DataType, following the typedef/type-parameter tables so that a type
// parameter such as `parameter type T = int` compares as its bound type. A name
// that never resolves to a built-in or a table entry (for instance a plain
// variable used as `type(v)`) is left unresolved so the caller does not fold
// it.
// §6.23 with §26.3, §8.23 and §6.25: the type a scope-qualified name in a type
// reference stands for. A typedef of a parameterized class is specialized,
// with arguments folded outside any module's scope; a package's or class's
// typedef is read under its "scope::name" key, or from a class the key misses,
// one declared inside a module. Nothing where the name resolves to none, or to
// a type carrying unpacked dimensions, which a data type alone does not hold.
static std::optional<DataType> ScopedTypeRefType(const DataType& dt,
                                                 const TypedefMap& typedefs,
                                                 const CompilationUnit* unit,
                                                 Arena& arena) {
  if (auto spec = SpecializeClassScopedType(dt, unit, {}, typedefs, arena)) {
    if (!spec->unpacked_dims.empty()) return std::nullopt;
    return spec->type;
  }
  auto it = typedefs.find(std::string(dt.scope_name) +
                          "::" + std::string(dt.type_name));
  if (it != typedefs.end()) return it->second;
  const DataType* in_class =
      FindClassScopedTypedefType(dt.scope_name, dt.type_name, unit);
  if (in_class != nullptr) return *in_class;
  return std::nullopt;
}

// Whether `e` is a scope resolution of one identifier by another, `p::t_s`.
static bool IsScopedTypeName(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kMemberAccess &&
         e->is_scope_resolution && e->lhs != nullptr &&
         e->lhs->kind == ExprKind::kIdentifier && e->rhs != nullptr &&
         e->rhs->kind == ExprKind::kIdentifier;
}

// The data type a type reference names as written, before any name in it is
// resolved: the one the parser read, or a name standing alone or behind a
// package's scope. Nothing for a type reference to an expression.
static std::optional<DataType> TypeRefWrittenType(const Expr* op) {
  if (op->type_value != nullptr) {
    // The data type the parser read, packed dimensions and signing included:
    // `type(bit[12:0])` is a 13-bit vector, where its name alone is `bit`.
    return *op->type_value;
  }
  if (!op->text.empty()) return TypeNameToDataType(op->text);
  if (op->lhs && op->lhs->kind == ExprKind::kIdentifier)
    return TypeNameToDataType(op->lhs->text);
  if (!IsScopedTypeName(op->lhs)) return std::nullopt;
  // `type(p::t_s)` with p a package reads as a scope resolution expression.
  DataType dt;
  dt.kind = DataTypeKind::kNamed;
  dt.scope_name = op->lhs->lhs->text;
  dt.type_name = op->lhs->rhs->text;
  return dt;
}

// Whether the type a type reference writes is a name alone, which may name a
// value rather than a type.
static bool IsBareName(const DataType& dt) {
  return dt.kind == DataTypeKind::kNamed && dt.scope_name.empty() &&
         dt.packed_dim_left == nullptr && dt.extra_packed_dims.empty();
}

// The type `dt` stands for once each name it is written by is read through:
// a built-in type keyword, a typedef, or a package's or class's typedef behind
// its scope. Nothing where a name resolves to none of them.
static std::optional<DataType> ThroughTypeNames(DataType dt,
                                                const TypedefMap& typedefs,
                                                const CompilationUnit* unit,
                                                Arena& arena) {
  for (int depth = 0; depth < 16 && dt.kind == DataTypeKind::kNamed; ++depth) {
    if (!dt.scope_name.empty()) {
      auto scoped = ScopedTypeRefType(dt, typedefs, unit, arena);
      if (!scoped) break;
      dt = *scoped;
      continue;
    }
    DataType builtin = TypeNameToDataType(dt.type_name);
    if (builtin.kind != DataTypeKind::kNamed) return builtin;
    auto it = typedefs.find(dt.type_name);
    if (it == typedefs.end()) break;
    dt = it->second;
  }
  if (dt.kind == DataTypeKind::kNamed) return std::nullopt;
  return dt;
}

std::optional<DataType> ElaboratorOperationRules::CalledFunctionType(
    const Expr* e) const {
  if (e == nullptr || e->kind != ExprKind::kCall ||
      (e->lhs != nullptr && e->lhs->kind != ExprKind::kIdentifier))
    return std::nullopt;
  if (const ModuleItem* fn = RegisteredConstFunc(e)) return fn->return_type;
  auto it = func_decls_.find(e->callee);
  if (it == func_decls_.end()) return std::nullopt;
  return it->second->return_type;
}

std::optional<DataType> ElaboratorOperationRules::ResolveTypeRefOperandType(
    const Expr* op, const RtlirModule* mod) const {
  if (!op || op->kind != ExprKind::kTypeRef) return std::nullopt;
  std::optional<DataType> written = TypeRefWrittenType(op);
  if (!written) written = CalledFunctionType(op->lhs);
  if (!written) return std::nullopt;
  DataType dt = *written;
  // §6.23: a name the module declares a net or variable by is an expression,
  // standing for the value's type, which a typedef or nettype names in turn.
  if (mod != nullptr && IsBareName(dt)) {
    std::string_view declared =
        DeclaredScopedName(dt.type_name, gen_prefix_scopes_, declared_names_);
    if (std::optional<DataType> value = NetOrVariableType(*mod, declared))
      dt = *value;
  }
  return ThroughTypeNames(dt, typedefs_, unit_, arena_);
}

// §6.23 — a comparison of two type references is a constant expression whose
// result is true exactly when the referenced types match per §6.22.1 (equality
// forms yield that truth value; inequality forms its negation). Fold such a
// comparison to 0/1 so it can drive an elaboration-time selection (e.g. a
// generate-if). Returns nullopt when this is not a two-type-reference
// comparison or either operand's type cannot be resolved.
std::optional<int64_t> ElaboratorOperationRules::EvalConstTypeRefCompare(
    const Expr* expr, const RtlirModule* mod) const {
  if (!IsTypeRefComparison(expr)) return std::nullopt;
  auto lhs_type = ResolveTypeRefOperandType(expr->lhs, mod);
  auto rhs_type = ResolveTypeRefOperandType(expr->rhs, mod);
  if (!lhs_type || !rhs_type) return std::nullopt;
  bool matched = TypesMatch(*lhs_type, *rhs_type);
  bool is_negated =
      expr->op == TokenKind::kBangEq || expr->op == TokenKind::kBangEqEq;
  return (matched != is_negated) ? 1 : 0;
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
// §7.2 with §6.23: nor is a `.` that selects a member of a variable, `p.f` of
// a structure `p`, which names no scope (NamesSelectableVariable).
bool ElaboratorOperationRules::IsHierarchicalMemberAccess(const Expr* e) const {
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution)
    return false;
  const Expr* root = e->lhs;
  while (root->kind == ExprKind::kMemberAccess && !root->is_scope_resolution)
    root = root->lhs;
  return !NamesSelectableVariable(root);
}

// The variable package `pkg` declares as `name`; null where it declares none.
static const ModuleItem* PackageVariable(const CompilationUnit& unit,
                                         std::string_view pkg,
                                         std::string_view name) {
  for (const PackageDecl* p : unit.packages) {
    if (p->name != pkg) continue;
    for (const ModuleItem* item : p->items) {
      if (item->kind == ModuleItemKind::kVarDecl && item->name == name)
        return item;
    }
  }
  return nullptr;
}

// Whether a variable declared with `type` has members a `.` selects: any but
// a class handle, whose property is an element of a dynamic object, and a
// virtual interface, which stands for an instance.
bool ElaboratorOperationRules::DeclaresSelectableType(
    const DataType& type) const {
  return type.kind != DataTypeKind::kVirtualInterface &&
         (type.kind != DataTypeKind::kNamed ||
          class_names_.count(type.type_name) == 0);
}

// Whether `root`, what a chain of `.` accesses starts from, names a variable
// whose members a `.` selects: one a package declares, written behind `::`
// (§26.3); one a block around the type operator declares, the innermost
// declaration of the name deciding; or one the module declares, a class
// handle and a virtual interface excepted.
bool ElaboratorOperationRules::NamesSelectableVariable(const Expr* root) const {
  if (root->kind == ExprKind::kMemberAccess) {
    const ModuleItem* var =
        PackageVariable(*unit_, root->lhs->text, root->rhs->text);
    return var != nullptr && DeclaresSelectableType(var->data_type);
  }
  for (auto decl = type_ref_block_vars_.rbegin();
       decl != type_ref_block_vars_.rend(); ++decl) {
    if (decl->first == root->text) return decl->second;
  }
  auto it = var_types_.find(root->text);
  return root->kind == ExprKind::kIdentifier && it != var_types_.end() &&
         it->second != DataTypeKind::kVirtualInterface &&
         class_var_names_.count(root->text) == 0;
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

void ElaboratorOperationRules::ValidateTypeRefArgs(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->data_type.type_ref_expr) {
      CheckTypeRefArgInner(item->data_type.type_ref_expr, item->loc);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForTypeRefArg(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForTypeRefArg(item->assign_rhs);
    }
  }
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
