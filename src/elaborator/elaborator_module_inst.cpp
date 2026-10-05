#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_child_type_params.h"
#include "elaborator/elaborator_gen_block_interfaces.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/elaborator_module_inst_internal.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

// The specialization arguments written on a parameterized class name, in the
// form DataType::type_params holds them in.
//
// Parser::ParseParameterizedScope in src/parser/expr_parser.cpp records
// `Buf#(byte)` onto the identifier node as has_param_spec, arg_names and
// elements, because an override value is parsed as an expression. That is a
// different shape from the DataType vector Parser::ParseTypeParamList in
// src/parser/parser_types.cpp builds for the declaration `Buf#(byte) v;`,
// which is the shape ResolveParameterizedType substitutes from. Each argument
// is a type written where an expression was parsed, so it converts through the
// same route the override value itself takes.
static std::vector<DataType> OverrideSpecializationArgs(
    const Expr* name, const CompilationUnit* unit, DiagEngine& diag,
    SourceLoc loc) {
  std::vector<DataType> args;
  args.reserve(name->elements.size());
  for (size_t i = 0; i < name->elements.size(); ++i) {
    DataType arg =
        TypeParamOverrideToDataType(name->elements[i], unit, diag, loc);
    if (i < name->arg_names.size()) arg.param_arg_name = name->arg_names[i];
    args.push_back(arg);
  }
  return args;
}

// Gives an override list written as `Buf#()` the class's own default
// arguments, so that the specialization it names survives the substitution.
//
// §8.25.1 (printed page 205) states that "the default specialization of a
// parameterized class is the specialization of the parameterized class with an
// empty parameter override list", so `Buf#()::elem_t` names elem_t with every
// parameter of Buf at the default its declaration gives. DataType carries no
// flag recording that `#(...)` was written, only the arguments themselves, so
// an empty list reaching ResolveParameterizedType is indistinguishable there
// from the unspecialized `Buf::elem_t` that function rejects. Filling the
// defaults here is what tells the two apart. A list that is not empty needs
// nothing, because ResolveParameterizedType supplies the default of every
// formal the list leaves unmentioned, whether the list binds by name or by
// position.
static void FillDefaultSpecializationArgs(std::vector<DataType>& args,
                                          const ClassDecl* cls) {
  if (!args.empty()) return;
  args = cls->param_types;
}

// §8.23 names a type parameter assignment as one of the contexts in which a
// class scope resolution may prefix a type name, so `.T(Frame::payload_t)`
// denotes the typedef `payload_t` declared in class `Frame`. The parse is a
// kMemberAccess with is_scope_resolution set, from Parser::MakeMemberAccess in
// src/parser/expr_parser.cpp. When the class and its typedef are visible
// the override binds to the type the typedef aliases; type_ref_expr is dropped
// for the reason ResolveClassScopedTypeRef drops it in
// src/elaborator/elaborator_validate_struct_types.cpp, namely that the
// alias has already been resolved and a leftover `type(...)` argument would be
// resolved a second time against the child's scope. When they are not visible
// the two halves of the name are kept in the shape Parser::ParseNamedType
// writes the declaration form `Frame::payload_t` in
// (src/parser/parser_types.cpp), so whatever resolves a named type
// later still has both. Returns a DataType left at kImplicit when the node is
// not a scope resolution over two identifiers.
//
// A prefix written with `#(...)` is a specialization instead of a plain class
// name. §8.25 (printed page 204) states that "a generic class is not a type;
// only a concrete specialization represents a type", and that two
// specializations are the same type only when all their parameters are the
// same, so `Buf#(byte)::elem_t` and `Buf#(shortint)::elem_t` are different
// types and neither is what the unspecialized `Buf` would give. Such a prefix
// therefore builds the named type ResolveParameterizedType substitutes into
// rather than reading the member's declared type as it stands.
static DataType ClassScopedOverrideToDataType(const Expr* expr,
                                              const CompilationUnit* unit,
                                              DiagEngine& diag, SourceLoc loc) {
  DataType dt;
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kIdentifier) {
    return dt;
  }
  if (expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return dt;
  }
  if (expr->lhs->has_param_spec) {
    const auto* cls = FindClassDecl(expr->lhs->text, unit);
    if (cls == nullptr) return dt;
    dt.kind = DataTypeKind::kNamed;
    dt.scope_name = expr->lhs->text;
    dt.type_name = expr->rhs->text;
    dt.type_params = OverrideSpecializationArgs(expr->lhs, unit, diag, loc);
    FillDefaultSpecializationArgs(dt.type_params, cls);
    // A specialization whose arguments do not reach the member leaves the
    // override naming no type, which ResolveChildTypeParam reports against
    // §23.10.2. Answering with the member's declared type instead would bind
    // the parameter to the unspecialized class, which is the silence that
    // report stands in place of.
    if (!ResolveParameterizedType(dt, unit, diag, loc)) return DataType{};
    return dt;
  }
  const DataType* resolved =
      FindClassScopedTypedefType(expr->lhs->text, expr->rhs->text, unit);
  if (resolved == nullptr) {
    dt.kind = DataTypeKind::kNamed;
    dt.scope_name = expr->lhs->text;
    dt.type_name = expr->rhs->text;
    return dt;
  }
  dt = *resolved;
  dt.type_ref_expr = nullptr;
  return dt;
}

// True when `expr` is a packed dimension written on a type rather than a select
// of a value. §7.4.1 writes a packed dimension as the range [msb:lsb], which
// Parser::ParseSelectExpr records as index and index_end with neither
// part-select flag set (src/parser/expr_parser.cpp); a bit select
// leaves index_end null and a +:/-: part select sets one of the flags, and
// neither of those names a type.
static bool IsPackedDimSelect(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kSelect &&
         expr->index != nullptr && expr->index_end != nullptr &&
         !expr->is_part_select_plus && !expr->is_part_select_minus;
}

// Peels the packed dimensions off `expr`, appending each to `sels` and
// returning the node they were written on. Parser::ParseSelectExpr hangs each
// select off the expression it follows (src/parser/expr_parser.cpp), so the
// first dimension written is the innermost node and `sels` comes out in the
// reverse of written order.
static const Expr* PeelPackedDimSelects(const Expr* expr,
                                        std::vector<const Expr*>& sels) {
  while (IsPackedDimSelect(expr)) {
    sels.push_back(expr);
    expr = expr->base;
  }
  return expr;
}

// §7.4.1 orders packed dimensions left to right with the leftmost the most
// significant, so a dimension written on the override precedes any the named
// type already carries: `T [3:0]`, where `typedef byte T`, is [3:0][7:0].
// `sels` is in the reverse of written order, as PeelPackedDimSelects leaves it.
static void PrependWrittenPackedDims(DataType& dt,
                                     const std::vector<const Expr*>& sels) {
  if (sels.empty()) return;
  std::vector<std::pair<Expr*, Expr*>> dims;
  dims.reserve(sels.size() + 1 + dt.extra_packed_dims.size());
  for (size_t n = sels.size(); n > 0; --n) {
    dims.push_back({sels[n - 1]->index, sels[n - 1]->index_end});
  }
  if (dt.packed_dim_left != nullptr) {
    dims.push_back({dt.packed_dim_left, dt.packed_dim_right});
  }
  dims.insert(dims.end(), dt.extra_packed_dims.begin(),
              dt.extra_packed_dims.end());
  dt.packed_dim_left = dims.front().first;
  dt.packed_dim_right = dims.front().second;
  dt.extra_packed_dims.assign(dims.begin() + 1, dims.end());
}

// The type named by the head of a type-parameter override, once its packed
// dimensions have been peeled off: a name (a keyword type, which
// Parser::ParseCastOrTypedPattern hands over as an identifier in
// src/parser/expr_parser.cpp, a typedef, or a class), or a class scope
// resolution. Anything else leaves the DataType at kImplicit.
static DataType OverrideHeadToDataType(const Expr* head,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag, SourceLoc loc) {
  if (head == nullptr) return DataType{};
  // A data_type an expression could not spell, `int unsigned` or `virtual
  // ifc`, arrives as the type Parser::ParseParamValueAssignment read
  // (src/parser/expr_parser.cpp).
  if (head->kind == ExprKind::kTypeRef && head->type_value != nullptr) {
    return *head->type_value;
  }
  if (head->kind == ExprKind::kIdentifier) {
    DataType dt = TypeNameToDataType(head->text);
    // §8.25 (printed page 204): a specialization is the generic class combined
    // with its arguments, and "a generic class is not a type; only a concrete
    // specialization represents a type". So `D#(4)` names a type where the bare
    // `D` names none when D leaves a parameter without a default, and the
    // arguments are what the declaration the override reaches is judged on.
    if (head->has_param_spec) {
      dt.type_params = OverrideSpecializationArgs(head, unit, diag, loc);
    }
    return dt;
  }
  if (head->kind == ExprKind::kMemberAccess && head->is_scope_resolution) {
    return ClassScopedOverrideToDataType(head, unit, diag, loc);
  }
  return DataType{};
}

// §6.20.3: convert the value of an instance parameter value assignment that
// binds a type parameter into the DataType it names.
// Parser::ParseParamValueEntry parses that value with ParseExpr
// in src/parser/parser_inst.cpp because the parse cannot know which
// of the child's parameters are type parameters, so the type has to be read
// back off the expression node the parse left. A returned DataType still at
// DataTypeKind::kImplicit means the value names no type, which is what lets the
// caller tell an assignment it cannot use from an absent one. Declared in
// elaborator_items_params.h, since Elaborator::ElaborateParamDecl reads the
// type an assignment names for a type parameter declared among a module's
// items through it as well.
DataType TypeParamOverrideToDataType(const Expr* expr,
                                     const CompilationUnit* unit,
                                     DiagEngine& diag, SourceLoc loc) {
  std::vector<const Expr*> sels;
  const Expr* head = PeelPackedDimSelects(expr, sels);
  DataType dt = OverrideHeadToDataType(head, unit, diag, loc);
  if (dt.kind == DataTypeKind::kImplicit) return dt;
  PrependWrittenPackedDims(dt, sels);
  return dt;
}

// §11.2.1 counts parameters among the operands a constant expression is made
// of, so an instance-array bound may name one. `scope` carries the values
// declared where the instantiation is written; without it a bound like [N:0]
// would not fold and the array would collapse to a single instance.
static uint32_t EvalInstDimSize(const Expr* left, const Expr* right,
                                const ScopeMap& scope) {
  if (left && right) {
    auto lv = ConstEvalInt(left, scope);
    auto rv = ConstEvalInt(right, scope);
    if (lv && rv) return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  } else if (left) {
    auto v = ConstEvalInt(left, scope);
    if (v && *v > 0) return static_cast<uint32_t>(*v);
  }
  return 0;
}

namespace {

// Removes any existing override for `pname` from `child_params`, preserving the
// relative order of the remaining entries.
void DropParamOverride(Elaborator::ParamList& child_params,
                       std::string_view pname) {
  Elaborator::ParamList kept;
  kept.reserve(child_params.size());
  for (const auto& e : child_params) {
    if (e.name != pname) kept.push_back(e);
  }
  child_params.swap(kept);
}

// "#()" returns every parameter to its module default: discard the
// instantiation's overrides and let the configuration own each one (§33.4.3).
//
// §33.4.3 (printed page 940) has the configuration's parameter override take
// precedence over a defparam on the same parameter, and the parameters the
// use clause returns to their defaults are every one the instance's
// assignment could name (OverridableParamNames) -- a `parameter` among the
// items of a module declared with no parameter port list among them
// (§6.20.1, printed 125-126), which the cleared assignment list leaves to
// its own value. The parameter port list's alone were locked before, so
// `defparam top.u.P = 9` in top after `instance top.u use #()` on `module c;
// parameter P = 2;` made P 9. A defparam on a type parameter is refused
// before the lock is read (§6.20.3), so locking one changes nothing.
void ResetAllConfigParams(const ModuleDecl* child_decl,
                          Elaborator::ParamList& child_params,
                          std::vector<std::string_view>& locked) {
  child_params.clear();
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    if (child_decl->type_param_names.count(dname) > 0) continue;
    if (dexpr) {
      if (auto val = ConstEvalInt(dexpr)) {
        child_params.push_back({dname, *val, dexpr});
      }
    }
  }
  const std::vector<std::string_view> kOwned =
      OverridableParamNames(child_decl);
  locked.insert(locked.end(), kOwned.begin(), kOwned.end());
}

// Resolves positional parameter overrides (#(v0, v1, ...)) against the child
// module's overridable parameters, appending evaluated values to child_params.
// §23.10 (printed page 763) with §6.20.1 (printed 125): those are the
// parameter port list's, or, for a module declared with no parameter port
// list, the `parameter` declarations among its items in declaration order,
// which OverridableParamNames answers; read from the port list alone, `vdff
// #(10,15)` over §23.10.2's own vdff (printed 766) was one value too many for
// a list of none.
void ResolvePositionalInstParams(const ModuleItem* item,
                                 const ModuleDecl* child_decl,
                                 const ScopeMap& parent_scope,
                                 Elaborator::ParamList& child_params,
                                 DiagEngine& diag) {
  const std::vector<std::string_view> kTargets =
      OverridableParamNames(child_decl);
  if (item->inst_params.size() > kTargets.size()) {
    diag.Error(item->loc,
               std::format("too many positional parameter overrides for module "
                           "'{}': {} provided, {} allowed",
                           item->inst_module, item->inst_params.size(),
                           kTargets.size()),
               Subclause("23.10.2.1"));
  }
  size_t n = std::min(item->inst_params.size(), kTargets.size());
  for (size_t i = 0; i < n; ++i) {
    auto* pexpr = item->inst_params[i].second;
    if (!pexpr) continue;
    PushInstParamAssignment(child_decl, kTargets[i], pexpr, parent_scope,
                            child_params);
  }
}

// Resolves named parameter overrides (#(.p(v), ...)) against the child module's
// overridable parameters, appending evaluated values to child_params. The
// parameters are the ones ResolvePositionalInstParams above binds by position,
// a module without a parameter port list having them among its items; read
// from the port list alone, `c #(.P(5))` over `module c; parameter P = 1;`
// was refused as naming no parameter of c.
void ResolveNamedInstParams(const ModuleItem* item,
                            const ModuleDecl* child_decl,
                            const ScopeMap& parent_scope,
                            Elaborator::ParamList& child_params,
                            DiagEngine& diag) {
  const std::vector<std::string_view> kNames =
      OverridableParamNames(child_decl);
  const std::unordered_set<std::string_view> kOverridable(kNames.begin(),
                                                          kNames.end());
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (kOverridable.count(pname) == 0) {
      diag.Error(item->loc,
                 std::format("module '{}' has no parameter '{}'",
                             item->inst_module, pname),
                 Subclause("23.10.2.2"));
      continue;
    }
    if (!pexpr) continue;
    PushInstParamAssignment(child_decl, pname, pexpr, parent_scope,
                            child_params);
  }
}

// Marks each parameter the configuration fixed so a later defparam cannot
// change it: a config override takes precedence over defparam (§33.4.3).
void MarkConfigLockedParams(
    RtlirModuleInst& inst, const std::vector<std::string_view>& config_locked) {
  if (!inst.resolved) return;
  for (auto pname : config_locked) {
    for (auto& p : inst.resolved->params) {
      if (p.name == pname) {
        p.config_locked = true;
        break;
      }
    }
  }
}

// Evaluates the instance array dimensions, appending each nonzero size to
// inst_dim_sizes and returning the product (total instance count, default 1).
uint32_t ComputeInstDimSizes(const ModuleItem* item, const ScopeMap& scope,
                             std::vector<uint32_t>& inst_dim_sizes) {
  uint32_t total_instances = 1;
  for (const auto& [left, right] : item->inst_dims) {
    uint32_t sz = EvalInstDimSize(left, right, scope);
    if (sz > 0) {
      inst_dim_sizes.push_back(sz);
      total_instances *= sz;
    }
  }
  return total_instances;
}

// Returns true when the instantiation supplied at least one positional
// (unnamed) parameter override (#(v0, v1, ...)).
bool InstUsesPositionalParams(const ModuleItem* item) {
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (pname.empty() && pexpr) return true;
  }
  return false;
}

// Reports a diagnostic for an instantiation of an unknown module, qualifying
// the name with its scope when one was specified.
void ReportUnknownModule(const ModuleItem* item, DiagEngine& diag) {
  if (item->inst_scope.empty())
    diag.Error(item->loc, std::format("unknown module '{}'", item->inst_module),
               Subclause("23.3.2"));
  else
    diag.Error(item->loc,
               std::format("unknown module '{}::{}'", item->inst_scope,
                           item->inst_module),
               Subclause("23.3.2"));
}

// Builds the scope used to evaluate configuration parameter-override
// expressions: the instance's parent scope augmented with the configuration's
// own localparams (§33.4.3).
ScopeMap BuildConfigOverrideScope(const ScopeMap& parent_scope,
                                  const ScopeMap& config_localparam_scope) {
  ScopeMap scope = parent_scope;
  for (const auto& [name, val] : config_localparam_scope) {
    scope[name] = val;
  }
  return scope;
}

// The dotted names a member-access chain is written with, outermost first, or
// nothing where the chain is not a pure one.
static std::vector<std::string_view> MemberAccessNames(const Expr* e) {
  std::vector<std::string_view> names;
  while (e != nullptr && e->kind == ExprKind::kMemberAccess) {
    if (e->rhs == nullptr) return {};
    names.insert(names.begin(), e->rhs->text);
    e = e->lhs;
  }
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return {};
  names.insert(names.begin(), e->text);
  return names;
}

// §33.4.3 (printed page 940): "Parameters identifiers shall be resolved
// starting in the parent scope of the instance", so a hierarchical reference
// in a configuration's override that names the configured instance's parent,
// `top.WIDTH` for `instance top.a1`, is that parent's parameter. It is folded
// here, where the parent's values are known: a scalar parameter becomes its
// value and a parameter array its name in the parent's scope, which an index
// -- a literal or a config localparam -- then selects in. A reference naming
// any other scope is left as it was written.
static Expr* ResolveParentReference(Expr* e, std::string_view parent_path,
                                    const ScopeMap& parent_scope,
                                    Arena& arena) {
  if (e == nullptr) return e;
  if (e->kind == ExprKind::kSelect && e->base != nullptr &&
      e->base->kind == ExprKind::kMemberAccess) {
    Expr* base =
        ResolveParentReference(e->base, parent_path, parent_scope, arena);
    if (base == e->base) return e;
    auto* copy = arena.Create<Expr>(*e);
    copy->base = base;
    return copy;
  }
  auto names = MemberAccessNames(e);
  if (names.size() < 2) return e;
  std::string scope_path;
  for (size_t i = 0; i + 1 < names.size(); ++i) {
    if (i > 0) scope_path += '.';
    scope_path.append(names[i]);
  }
  bool names_parent =
      parent_path == scope_path ||
      (parent_path.size() > scope_path.size() &&
       parent_path.ends_with(scope_path) &&
       parent_path[parent_path.size() - scope_path.size() - 1] == '.');
  if (!names_parent) return e;
  std::string_view param = names.back();
  if (auto it = parent_scope.find(param); it != parent_scope.end()) {
    auto* value = arena.Create<Expr>();
    value->kind = ExprKind::kIntegerLiteral;
    value->int_val = static_cast<uint64_t>(it->second);
    value->range = e->range;
    return value;
  }
  auto* ident = arena.Create<Expr>();
  ident->kind = ExprKind::kIdentifier;
  ident->text = param;
  ident->range = e->range;
  return ident;
}

// Applies one configuration override's explicit per-parameter values onto
// child_params, recording each touched parameter in `locked`. A present
// expression sets a new value, a null one ("(.p())") leaves the parameter at
// its module default; either way the configuration now owns the parameter
// (§33.4.3).
void ApplyConfigOverrideParams(
    const std::vector<std::pair<std::string_view, Expr*>>& override_params,
    Elaborator::ParamList& child_params, const ScopeMap& scope,
    std::vector<std::string_view>& locked) {
  for (const auto& [pname, pexpr] : override_params) {
    DropParamOverride(child_params, pname);
    if (pexpr) {
      if (auto val = ConstEvalInt(pexpr, scope)) {
        child_params.push_back({pname, *val, pexpr});
      }
    }
    locked.push_back(pname);
  }
}

using VarArrayInfoMap =
    std::unordered_map<std::string_view, Elaborator::VarArrayInfo>;

// Shared context for §23.3.3.5 instance-array expansion: the arena for
// synthesizing per-instance connection expressions, the parent module (for
// signal widths), the parent's unpacked-array shapes, and the parent's
// parameter scope, which folds the packed dimension of a connected signal so a
// synthesized part-select can be written in its declared range.
struct InstArrayDistribCtx {
  Arena& arena;
  const RtlirModule* parent_mod;
  const VarArrayInfoMap& var_array_info;
  const ScopeMap& parent_scope;
};

Expr* MakeIntLitExpr(Arena& arena, uint64_t v) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = v;
  return e;
}

// `base[idx]` (single element/bit select).
Expr* MakeElementSelectExpr(Arena& arena, Expr* base, uint32_t idx) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = MakeIntLitExpr(arena, idx);
  return e;
}

// `base[base_index +: width]` (ascending indexed part-select). `base_index` is
// an index of `base` in the range its declaration was written with, which is
// what §11.5.1 resolves the select against.
Expr* MakePartSelectPlusExpr(Arena& arena, Expr* base, int64_t base_index,
                             uint32_t width) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = MakeIntLitExpr(arena, static_cast<uint64_t>(base_index));
  e->index_end = MakeIntLitExpr(arena, width);
  e->is_part_select_plus = true;
  return e;
}

// §11.5.1: the base index the part-select for instance `position` of a `total`
// instance array is written with. The rightmost instance takes the least
// significant bits of the connection (§23.3.3.5), so `position` fixes how far
// above that end this instance's run starts, and the range the connection was
// declared with turns that into the index naming it. A connection that is not a
// named signal -- a concatenation the uniform-element case declined -- carries
// no declaration of its own and is addressed as [width-1:0].
int64_t ConnPartSelectBase(const InstArrayDistribCtx& ctx,
                           const RtlirPortBinding& binding, uint32_t position,
                           uint32_t total) {
  const Expr* conn = binding.connection;
  uint32_t port_width = binding.width;
  PackedRange range =
      (conn->kind == ExprKind::kIdentifier)
          ? SignalDeclaredRange(conn->text, ctx.parent_mod, ctx.parent_scope)
          : PackedRange::Implicit(port_width * total);
  return range.PlusSelectBase(static_cast<int64_t>(position) * port_width,
                              port_width);
}

// Total width of a concatenation whose elements are all named signals, or 0 if
// any element is not a simple identifier.
uint32_t ConcatConnWidth(const Expr* conn, const RtlirModule* mod) {
  uint32_t w = 0;
  for (const Expr* el : conn->elements) {
    if (!el || el->kind != ExprKind::kIdentifier) return 0;
    w += FindSignalWidth(el->text, mod);
  }
  return w;
}

// True when a concatenation has exactly `total` elements and each is a named
// signal of width `port_width`, so position `p` maps cleanly to one element.
bool ConcatElementsUniform(const Expr* conn, uint32_t total,
                           uint32_t port_width, const RtlirModule* mod) {
  if (conn->elements.size() != total) return false;
  for (const Expr* el : conn->elements) {
    if (!el || el->kind != ExprKind::kIdentifier) return false;
    if (FindSignalWidth(el->text, mod) != port_width) return false;
  }
  return true;
}

// §23.3.3.5 (printed page 748): an unpacked array connection is split across
// an array of instances, "each element of the port connection shall be matched
// to the port left index to left index, right index to right index", so the
// instance `position` places from the right stands `total - 1 - position`
// places from the left and takes the element that far from the array's left
// bound. A variable's bounds are its declared ones; a net array is read as
// written `[size]`, from 0. Empty where the name is no unpacked array, a
// variable's or a net's.
std::optional<int64_t> UnpackedElementForInstance(
    const InstArrayDistribCtx& ctx, std::string_view name, uint32_t position,
    uint32_t total) {
  const auto kFromLeft = static_cast<int64_t>(total - 1 - position);
  auto it = ctx.var_array_info.find(name);
  if (it != ctx.var_array_info.end() && it->second.num_unpacked_dims > 0) {
    if (it->second.declared_dims.empty()) return kFromLeft;
    const auto& dim = it->second.declared_dims.front();
    return dim.left <= dim.right ? dim.left + kFromLeft : dim.left - kFromLeft;
  }
  for (const auto& net : ctx.parent_mod->nets) {
    if (net.name == name && net.num_unpacked_dims > 0) return kFromLeft;
  }
  return std::nullopt;
}

// §23.3.3.5: rewrite one port connection for the instance at array position
// `position` (0 = least-significant / right index). An unpacked-array
// connection maps element-by-position; a packed connection whose width is
// port_width*total is part-selected (rightmost instance to the LSB); an
// equal-width connection is replicated to every instance.
Expr* DistributeInstanceConnection(const InstArrayDistribCtx& ctx,
                                   const RtlirPortBinding& binding,
                                   uint32_t position, uint32_t total) {
  Expr* conn = binding.connection;
  uint32_t port_width = binding.width;
  if (!conn || port_width == 0 || total < 2) return conn;

  if (conn->kind == ExprKind::kIdentifier) {
    if (auto index =
            UnpackedElementForInstance(ctx, conn->text, position, total)) {
      return MakeElementSelectExpr(ctx.arena, conn,
                                   static_cast<uint32_t>(*index));
    }
    if (FindSignalWidth(conn->text, ctx.parent_mod) == port_width * total) {
      return MakePartSelectPlusExpr(
          ctx.arena, conn, ConnPartSelectBase(ctx, binding, position, total),
          port_width);
    }
    return conn;
  }

  if (conn->kind == ExprKind::kConcatenation &&
      ConcatConnWidth(conn, ctx.parent_mod) == port_width * total) {
    if (ConcatElementsUniform(conn, total, port_width, ctx.parent_mod)) {
      // Concatenation elements are stored most-significant first.
      return conn->elements[total - 1 - position];
    }
    return MakePartSelectPlusExpr(
        ctx.arena, conn, ConnPartSelectBase(ctx, binding, position, total),
        port_width);
  }
  return conn;
}

// Materializes a single-dimension instance array `c[left:right]` as `total`
// separate instances, each named `c[idx]` and carrying its distributed port
// connections (§23.3.3.5). The resolved child module is shared across copies;
// per-instance variable storage is created later under each instance's prefix.
void PushInstanceArray(const InstArrayDistribCtx& ctx, RtlirModule* mod,
                       const RtlirModuleInst& base, int64_t left,
                       int64_t right) {
  auto total = static_cast<uint32_t>(std::abs(left - right) + 1);
  int64_t step = (right <= left) ? 1 : -1;
  for (uint32_t p = 0; p < total; ++p) {
    int64_t idx = right + step * static_cast<int64_t>(p);
    RtlirModuleInst copy = base;
    // §37.11: the element records the array it belongs to and its index,
    // which its expanded name alone does not say.
    copy.array = {base.simple_inst_name, left, right, idx};
    std::string name = std::format("{}[{}]", base.inst_name, idx);
    auto* buf = ctx.arena.AllocString(name.c_str(), name.size());
    copy.inst_name = std::string_view(buf, name.size());
    for (auto& b : copy.port_bindings) {
      b.connection = DistributeInstanceConnection(ctx, b, p, total);
    }
    mod->children.push_back(std::move(copy));
  }
}

// Appends `inst` to `mod`, expanding a single-dimension instance array into one
// distributed instance per index (§23.3.3.5). Other forms append a single
// instance unchanged.
void AppendModuleInstOrArray(const InstArrayDistribCtx& ctx, RtlirModule* mod,
                             const RtlirModuleInst& inst,
                             const ModuleItem* item, const ScopeMap& scope) {
  std::optional<int64_t> arr_left;
  std::optional<int64_t> arr_right;
  if (item->inst_dims.size() == 1) {
    if (item->inst_range_left)
      arr_left = ConstEvalInt(item->inst_range_left, scope);
    if (item->inst_range_right)
      arr_right = ConstEvalInt(item->inst_range_right, scope);
    // §23.3.2 writes an instance's dimension as an unpacked_dimension, whose
    // `[size]` form §7.4.2 makes `[0:size-1]`: `leaf arr[2]()` is arr[0] and
    // arr[1]. Read as a range with no right bound it was one instance.
    if (arr_left && item->inst_range_right == nullptr) {
      arr_right = *arr_left - 1;
      arr_left = 0;
      if (*arr_right < 0) arr_left.reset();
    }
  }
  if (arr_left && arr_right) {
    PushInstanceArray(ctx, mod, inst, *arr_left, *arr_right);
  } else {
    mod->children.push_back(inst);
  }
}

}  // namespace

// Resolves the instantiation's own parameter overrides into child_params,
// dispatching on whether they were written positionally or by name. Declared in
// elaborator_module_inst_internal.h so the other elaborator translation units
// that instantiate a module can reuse it.
void ResolveInstParams(const ModuleItem* item, const ModuleDecl* child_decl,
                       const ScopeMap& parent_scope,
                       Elaborator::ParamList& child_params, DiagEngine& diag) {
  if (InstUsesPositionalParams(item)) {
    ResolvePositionalInstParams(item, child_decl, parent_scope, child_params,
                                diag);
  } else {
    ResolveNamedInstParams(item, child_decl, parent_scope, child_params, diag);
  }
}

void Elaborator::ApplyConfigParamOverrides(
    const ModuleItem* item, const ModuleDecl* child_decl,
    Elaborator::ParamList& child_params, const ScopeMap& parent_scope,
    std::vector<std::string_view>& locked) {
  if (config_inst_path_.empty()) return;
  if (instance_param_overrides_.empty() && cell_param_overrides_.empty()) {
    return;
  }

  // Parameter identifiers resolve in the instance's parent scope, augmented
  // with the configuration's own localparams (§33.4.3).
  ScopeMap scope =
      BuildConfigOverrideScope(parent_scope, config_localparam_scope_);
  std::string_view parent_path = config_inst_path_;
  parent_path = parent_path.substr(0, parent_path.rfind('.'));
  auto apply = [&](const ConfigParamOverride& ov) {
    if (ov.reset_all) ResetAllConfigParams(child_decl, child_params, locked);
    auto params = ov.params;
    for (auto& assignment : params) {
      assignment.second = ResolveParentReference(assignment.second, parent_path,
                                                 parent_scope, arena_);
    }
    ApplyConfigOverrideParams(
        AssignableConfigParams(child_decl, params, ov.loc, diag_), child_params,
        scope, locked);
  };
  // §33.4.1.4: a cell clause's overrides reach every instance of the cell; an
  // instance clause, the more specific selection (§33.4.1.6), is applied after
  // it and so decides a parameter both name.
  for (const auto& ov : cell_param_overrides_) {
    if (ov.inst_path == item->inst_module) apply(ov);
  }
  for (const auto& ov : instance_param_overrides_) {
    if (ov.inst_path == config_inst_path_) apply(ov);
  }
}

void Elaborator::ElaborateModuleInst(ModuleItem* item, RtlirModule* mod) {
  // §27.4: a loop generate block, "even if the begin-end keywords are absent
  // ... is still a generate block, which, like all generate blocks, comprises a
  // separate scope and a new level of hierarchy when it is instantiated". One
  // instantiation written in a loop body is therefore elaborated once per
  // iteration into a different scope each time, and declares its name afresh
  // rather than again. The name is registered under the generate prefix that
  // tells those scopes apart; outside a generate block ScopedName hands the
  // name back unchanged, so a repeat at module level is still a redeclaration.
  //
  // The same subclause makes each instance of the block "a separate scope and a
  // new level of hierarchy", so the record of the instantiation has to carry
  // the scoped name as well as the redeclaration check does. Taking the raw
  // name for RtlirModuleInst::inst_name and for current_inst_path_ gave every
  // iteration one name and one instance path, which Lowerer::LowerChildModules
  // keys an instance's declarations on. ScopedName is asked once and answers
  // all three; ScopedName("") returns the generate prefix itself, which would
  // name an unnamed instantiation after the block holding it.
  std::string_view scoped_inst_name =
      item->inst_name.empty() ? item->inst_name : ScopedName(item->inst_name);
  if (!item->inst_name.empty() &&
      !declared_names_.insert(scoped_inst_name).second) {
    diag_.Error(item->loc,
                std::format("redeclaration of '{}'", item->inst_name),
                Subclause("23.9"));
  }
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = scoped_inst_name;
  // §23.6 reads a hierarchical name one step at a time, and the instance's own
  // name, set here, and the generate block steps above it, which
  // EnterGenBlockInstance sets below, are the steps this instance answers
  // with. inst_name is the two run together, which is the name the flattened
  // design stores but not a name any path can be matched against.
  inst.simple_inst_name = item->inst_name;

  std::string saved_inst_path = current_inst_path_;
  if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
  current_inst_path_.append(scoped_inst_name.data(), scoped_inst_name.size());
  std::string saved_config_path = std::exchange(
      config_inst_path_,
      HierInstancePath(config_inst_path_, gen_block_path_, item->inst_name));

  // §23.4: a name that resolves out of nested_module_decls_ names a module
  // declared inside this one, which sees this module's names.
  inst.is_nested_decl = nested_module_decls_.find(item->inst_module) !=
                        nested_module_decls_.end();
  auto* child_decl = FindModuleInScope(item->inst_module);
  if (!child_decl) child_decl = PackageCheckerNamedBy(item, mod, unit_);
  if (!child_decl) {
    if (!ReportConfigRuleBindingNothing(unit_, item, diag_))
      ReportUnknownModule(item, diag_);
    mod->children.push_back(inst);
    current_inst_path_ = std::move(saved_inst_path);
    config_inst_path_ = std::move(saved_config_path);
    return;
  }

  EnterGenBlockInstance(inst, child_decl,
                        {gen_block_path_, gen_loop_consts_, gen_prefix_scopes_},
                        interface_inst_types_);
  auto parent_scope = BuildParamScope(mod);
  ElaborateChildInstance(inst, item, child_decl, mod, parent_scope);
  BindPorts(inst, item, mod, child_decl);

  std::vector<uint32_t> inst_dim_sizes;
  uint32_t total_instances =
      ComputeInstDimSizes(item, parent_scope, inst_dim_sizes);

  if (!item->inst_dims.empty()) {
    ValidateInstanceArrayPorts(inst, item, mod, inst_dim_sizes,
                               total_instances);
  } else {
    ValidateUnpackedArrayPorts(inst, item, mod);
  }

  CheckInstancePorts(inst, item, mod);
  CoerceDrivenInputPorts(inst, mod);
  inst.attrs = ResolveAttributes(item->attrs, diag_);
  // §28.3.5: an instance-array range shall be given by two constant
  // expressions; a non-constant bound in a [lhi:rhi] range is an error, the
  // same rule the gate/switch-array path enforces.
  if (item->inst_range_left && item->inst_range_right &&
      (!ConstEvalInt(item->inst_range_left, parent_scope) ||
       !ConstEvalInt(item->inst_range_right, parent_scope))) {
    diag_.Error(item->loc,
                "instance array range bound must be a constant expression",
                Subclause("28.3.5"));
  }
  InstArrayDistribCtx dctx{arena_, mod, var_array_info_, parent_scope};
  AppendModuleInstOrArray(dctx, mod, inst, item, parent_scope);
  current_inst_path_ = std::move(saved_inst_path);
  config_inst_path_ = std::move(saved_config_path);
}

void Elaborator::ElaborateChildInstance(RtlirModuleInst& inst,
                                        const ModuleItem* item,
                                        ModuleDecl* child_decl,
                                        RtlirModule* mod,
                                        const ScopeMap& parent_scope) {
  auto saved_nested = nested_module_decls_;
  Elaborator::ParamList child_params;
  ResolveInstParams(item, child_decl, parent_scope, child_params, diag_);

  // A configuration may override (or reset) this instance's parameters on top
  // of whatever the instantiation specified (§33.4.3).
  std::vector<std::string_view> config_locked;
  ApplyConfigParamOverrides(item, child_decl, child_params, parent_scope,
                            config_locked);

  // §6.20.3/§23.10: publish the child's type-parameter substitutions into the
  // shared typedef map so its dependent declarations resolve against the chosen
  // types, then restore the map once the child has been elaborated.
  auto applied_type_params = ApplyChildTypeParams(
      TypeParamSourcesFor(item, instance_param_overrides_, config_inst_path_),
      child_decl, typedefs_, unit_, diag_);
  // §16.15: the default disable iff extends to a nested declaration and not
  // into an instance of a module declared elsewhere. §23.4 makes this scope's
  // names visible inside such a declaration as well, whether the instance is
  // written out here or implied by InstantiateImplicitNestedModules, so the
  // same names are handed to ElaborateModule either way: without them every
  // implicit net the nested module makes for an outer name counted as its own,
  // and an instance materialized a net shadowing the outer one. Which names
  // §6.10 settles by the declaration's place in the text rather than the
  // instance's, so BeginNestedDeclScope prefers the snapshot ElaborateItems
  // took there over the names declared so far.
  if (inst.is_nested_decl) {
    nested_default_disable_iff_ = mod->default_disable_iff;
    nested_default_clock_ = DefaultClockingEvent(mod);
    BeginNestedDeclScope(child_decl, CaptureCurrentScopeNames());
  }
  if (child_decl->decl_kind == ModuleDeclKind::kChecker) {
    pending_checker_actuals_ =
        BindCheckerActuals(item, child_decl, parent_scope);
    pending_checker_tree_actuals_ = CheckerTreeActuals(item, child_decl);
  }
  pending_type_param_types_ = std::move(applied_type_params.written);
  inst.resolved = ElaborateModule(child_decl, child_params);
  RestoreChildTypeParams(typedefs_, applied_type_params.saved);
  nested_module_decls_ = std::move(saved_nested);
  MarkConfigLockedParams(inst, config_locked);
}

void Elaborator::CheckInstancePorts(const RtlirModuleInst& inst,
                                    const ModuleItem* item, RtlirModule* mod) {
  CheckPortCoercion(inst, item->loc);
  ReportActualsOnlyACheckerTakes(inst, item, diag_);
  CheckUwirePortMerge(inst, item, mod);
  CheckInterconnectPortMerge(inst, item, mod);
}

}  // namespace delta
