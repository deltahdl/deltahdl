#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_module_inst_internal.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static DataType TypeParamOverrideToDataType(const Expr* expr,
                                            const CompilationUnit* unit);

// The specialization arguments written on a parameterized class name, in the
// form DataType::type_params holds them in.
//
// Parser::ParseParameterizedScope at src/parser/expr_parser.cpp:689 records
// `Buf#(byte)` onto the identifier node as has_param_spec, arg_names and
// elements, because an override value is parsed as an expression. That is a
// different shape from the DataType vector Parser::ParseTypeParamList at
// src/parser/parser_types.cpp:257 builds for the declaration `Buf#(byte) v;`,
// which is the shape ResolveParameterizedType substitutes from. Each argument
// is a type written where an expression was parsed, so it converts through the
// same route the override value itself takes.
static std::vector<DataType> OverrideSpecializationArgs(
    const Expr* name, const CompilationUnit* unit) {
  std::vector<DataType> args;
  args.reserve(name->elements.size());
  for (size_t i = 0; i < name->elements.size(); ++i) {
    DataType arg = TypeParamOverrideToDataType(name->elements[i], unit);
    if (i < name->arg_names.size()) arg.param_arg_name = name->arg_names[i];
    args.push_back(arg);
  }
  return args;
}

// Fills the arguments an override list leaves out from the class's own
// defaults.
//
// §8.25.1 (printed page 205) states that "the default specialization of a
// parameterized class is the specialization of the parameterized class with an
// empty parameter override list", so `Buf#()::elem_t` names elem_t with every
// parameter of Buf at the default its declaration gives, and a list shorter
// than the parameter list leaves the rest there the same way. A named argument
// binds to a formal by name rather than by position, which the positional fill
// here would get wrong, so a list carrying one is left as it was written.
static void FillDefaultSpecializationArgs(std::vector<DataType>& args,
                                          const ClassDecl* cls) {
  for (const auto& arg : args) {
    if (!arg.param_arg_name.empty()) return;
  }
  for (size_t i = args.size(); i < cls->param_types.size(); ++i) {
    args.push_back(cls->param_types[i]);
  }
}

// §8.23 names a type parameter assignment as one of the contexts in which a
// class scope resolution may prefix a type name, so `.T(Frame::payload_t)`
// denotes the typedef `payload_t` declared in class `Frame`. The parse is a
// kMemberAccess with is_scope_resolution set, from Parser::MakeMemberAccess at
// src/parser/expr_parser.cpp:622. When the class and its typedef are visible
// the override binds to the type the typedef aliases; type_ref_expr is dropped
// for the reason ResolveClassScopedTypeRef drops it at
// src/elaborator/elaborator_validate_struct_types.cpp:124, namely that the
// alias has already been resolved and a leftover `type(...)` argument would be
// resolved a second time against the child's scope. When they are not visible
// the two halves of the name are kept in the shape Parser::ParseNamedType
// writes the declaration form `Frame::payload_t` in
// (src/parser/parser_types.cpp:308-309), so whatever resolves a named type
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
                                              const CompilationUnit* unit) {
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
    dt.type_params = OverrideSpecializationArgs(expr->lhs, unit);
    FillDefaultSpecializationArgs(dt.type_params, cls);
    // A specialization whose arguments do not reach the member leaves the
    // override naming no type, which ResolveChildTypeParam reports against
    // §23.10.2. Answering with the member's declared type instead would bind
    // the parameter to the unspecialized class, which is the silence that
    // report stands in place of.
    if (!ResolveParameterizedType(dt, unit)) return DataType{};
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
// part-select flag set (src/parser/expr_parser.cpp:923-940); a bit select
// leaves index_end null and a +:/-: part select sets one of the flags, and
// neither of those names a type.
static bool IsPackedDimSelect(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kSelect &&
         expr->index != nullptr && expr->index_end != nullptr &&
         !expr->is_part_select_plus && !expr->is_part_select_minus;
}

// Peels the packed dimensions off `expr`, appending each to `sels` and
// returning the node they were written on. Parser::ParseSelectExpr hangs each
// select off the expression it follows (src/parser/expr_parser.cpp:736), so the
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
// Parser::ParseCastOrTypedPattern hands over as an identifier at
// src/parser/expr_parser.cpp:581-587, a typedef, or a class), or a class scope
// resolution. Anything else leaves the DataType at kImplicit.
static DataType OverrideHeadToDataType(const Expr* head,
                                       const CompilationUnit* unit) {
  if (head == nullptr) return DataType{};
  if (head->kind == ExprKind::kIdentifier)
    return TypeNameToDataType(head->text);
  if (head->kind == ExprKind::kMemberAccess && head->is_scope_resolution) {
    return ClassScopedOverrideToDataType(head, unit);
  }
  return DataType{};
}

// §6.20.3: convert the value of an instance parameter value assignment that
// binds a type parameter into the DataType it names.
// Parser::ParseParamValueEntry parses that value with ParseExpr
// (src/parser/parser_inst.cpp:122 and :128) because the parse cannot know which
// of the child's parameters are type parameters, so the type has to be read
// back off the expression node the parse left. A returned DataType still at
// DataTypeKind::kImplicit means the value names no type, which is what lets the
// caller tell an assignment it cannot use from an absent one.
static DataType TypeParamOverrideToDataType(const Expr* expr,
                                            const CompilationUnit* unit) {
  std::vector<const Expr*> sels;
  const Expr* head = PeelPackedDimSelects(expr, sels);
  DataType dt = OverrideHeadToDataType(head, unit);
  if (dt.kind == DataTypeKind::kImplicit) return dt;
  PrependWrittenPackedDims(dt, sels);
  return dt;
}

static bool InstParamsArePositional(const ModuleItem* item) {
  for (const auto& [n, e] : item->inst_params)
    if (n.empty() && e) return true;
  return false;
}

static const Expr* NamedTypeParamOverride(const ModuleItem* item,
                                          std::string_view pname) {
  for (const auto& [n, e] : item->inst_params)
    if (n == pname) return e;
  return nullptr;
}

// A positional override maps to the index of `pname` among the overridable
// (non-localparam) parameters, mirroring ResolvePositionalInstParams.
static const Expr* PositionalTypeParamOverride(const ModuleItem* item,
                                               const ModuleDecl* child_decl,
                                               std::string_view pname) {
  size_t idx = 0;
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    if (dname == pname)
      return idx < item->inst_params.size() ? item->inst_params[idx].second
                                            : nullptr;
    ++idx;
  }
  return nullptr;
}

// Locate the instantiation override expression for the type parameter `pname`,
// honoring both the named (.T(x)) and positional (#(x, ...)) forms (the two are
// never mixed -- the parser rejects that).
static const Expr* FindTypeParamOverrideExpr(const ModuleItem* item,
                                             const ModuleDecl* child_decl,
                                             std::string_view pname) {
  if (InstParamsArePositional(item))
    return PositionalTypeParamOverride(item, child_decl, pname);
  return NamedTypeParamOverride(item, pname);
}

// A saved typedef-map entry, so a type-parameter substitution made for one
// child elaboration can be undone afterwards (the map is shared across
// modules).
struct SavedTypedef {
  std::string_view name;
  bool existed = false;
  DataType prev;
};

// §23.10.2/§6.20.3: the type the child's type parameter at index `i` takes for
// this instantiation -- the instance parameter value assignment when one names
// a type, otherwise the type the declaration defaulted to. Returns nothing,
// having reported, when the assignment names no type, and when there is neither
// an assignment nor a default (§6.20.1). Reporting an assignment that names no
// type is what keeps it apart from an absent one: falling back to the default
// there would elaborate the child against a type the source did not write, and
// the mismatch would surface as a wrong width rather than as a report.
static std::optional<DataType> ResolveChildTypeParam(
    const ModuleItem* item, const ModuleDecl* child_decl, size_t i,
    const CompilationUnit* unit, DiagEngine& diag) {
  std::string_view pname = child_decl->params[i].first;
  const Expr* ov = FindTypeParamOverrideExpr(item, child_decl, pname);
  if (ov != nullptr) {
    DataType resolved = TypeParamOverrideToDataType(ov, unit);
    if (resolved.kind != DataTypeKind::kImplicit) return resolved;
    diag.Error(item->loc,
               std::format("parameter value assignment for type parameter '{}' "
                           "of '{}' does not name a type",
                           pname, child_decl->name),
               Subclause("23.10.2"));
    return std::nullopt;
  }
  if (i < child_decl->param_types.size() &&
      child_decl->param_types[i].kind != DataTypeKind::kImplicit) {
    return child_decl->param_types[i];
  }
  diag.Error(item->loc,
             std::format("type parameter '{}' of '{}' has no default type "
                         "and no override at instantiation",
                         pname, child_decl->name),
             Subclause("6.20.1"));
  return std::nullopt;
}

// §6.20.3/§23.10: resolve each of the child's type parameters to a concrete
// type and publish it in `typedefs` so the child's dependent declarations
// elaborate against the chosen type. A type parameter whose type
// ResolveChildTypeParam could not settle publishes nothing, so the child's
// declarations that depend on it are left unresolved rather than bound to a
// type the instantiation did not ask for. Returns the prior entries so the
// caller can restore the shared map after the child is elaborated.
static std::vector<SavedTypedef> ApplyChildTypeParams(
    const ModuleItem* item, const ModuleDecl* child_decl, TypedefMap& typedefs,
    const CompilationUnit* unit, DiagEngine& diag) {
  std::vector<SavedTypedef> saved;
  for (size_t i = 0; i < child_decl->params.size(); ++i) {
    std::string_view pname = child_decl->params[i].first;
    if (child_decl->type_param_names.count(pname) == 0) continue;
    auto resolved = ResolveChildTypeParam(item, child_decl, i, unit, diag);
    if (!resolved) continue;
    SavedTypedef s;
    s.name = pname;
    auto it = typedefs.find(pname);
    s.existed = it != typedefs.end();
    if (s.existed) s.prev = it->second;
    saved.push_back(s);
    typedefs[pname] = *resolved;
  }
  return saved;
}

static void RestoreChildTypeParams(TypedefMap& typedefs,
                                   const std::vector<SavedTypedef>& saved) {
  for (const auto& s : saved) {
    if (s.existed)
      typedefs[s.name] = s.prev;
    else
      typedefs.erase(s.name);
  }
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
    if (e.first != pname) kept.push_back(e);
  }
  child_params.swap(kept);
}

// "#()" returns every parameter to its module default: discard the
// instantiation's overrides and let the configuration own each one (§33.4.3).
void ResetAllConfigParams(const ModuleDecl* child_decl,
                          Elaborator::ParamList& child_params,
                          std::vector<std::string_view>& locked) {
  child_params.clear();
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    if (child_decl->type_param_names.count(dname) > 0) continue;
    locked.push_back(dname);
    if (dexpr) {
      if (auto val = ConstEvalInt(dexpr)) {
        child_params.push_back({dname, *val});
      }
    }
  }
}

// Resolves positional parameter overrides (#(v0, v1, ...)) against the child
// module's overridable parameters, appending evaluated values to child_params.
void ResolvePositionalInstParams(const ModuleItem* item,
                                 const ModuleDecl* child_decl,
                                 const ScopeMap& parent_scope,
                                 Elaborator::ParamList& child_params,
                                 DiagEngine& diag) {
  std::vector<std::string_view> targets;
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    targets.push_back(dname);
  }
  if (item->inst_params.size() > targets.size()) {
    diag.Error(item->loc,
               std::format("too many positional parameter overrides for module "
                           "'{}': {} provided, {} allowed",
                           item->inst_module, item->inst_params.size(),
                           targets.size()),
               Subclause("23.10.2.1"));
  }
  size_t n = std::min(item->inst_params.size(), targets.size());
  for (size_t i = 0; i < n; ++i) {
    auto* pexpr = item->inst_params[i].second;
    if (!pexpr) continue;
    auto val = ConstEvalInt(pexpr, parent_scope);
    if (val) child_params.push_back({targets[i], *val});
  }
}

// Resolves named parameter overrides (#(.p(v), ...)) against the child module's
// overridable parameters, appending evaluated values to child_params.
void ResolveNamedInstParams(const ModuleItem* item,
                            const ModuleDecl* child_decl,
                            const ScopeMap& parent_scope,
                            Elaborator::ParamList& child_params,
                            DiagEngine& diag) {
  std::unordered_set<std::string_view> overridable;
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    overridable.insert(dname);
  }
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (overridable.count(pname) == 0) {
      diag.Error(item->loc,
                 std::format("module '{}' has no parameter '{}'",
                             item->inst_module, pname),
                 Subclause("23.10.2.2"));
      continue;
    }
    if (!pexpr) continue;
    auto val = ConstEvalInt(pexpr, parent_scope);
    if (val) child_params.push_back({pname, *val});
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
        child_params.push_back({pname, *val});
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
    auto it = ctx.var_array_info.find(conn->text);
    if (it != ctx.var_array_info.end() && it->second.num_unpacked_dims > 0) {
      return MakeElementSelectExpr(ctx.arena, conn, position);
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
    const ModuleDecl* child_decl, Elaborator::ParamList& child_params,
    const ScopeMap& parent_scope, std::vector<std::string_view>& locked) {
  if (instance_param_overrides_.empty() || current_inst_path_.empty()) return;

  // Parameter identifiers resolve in the instance's parent scope, augmented
  // with the configuration's own localparams (§33.4.3).
  ScopeMap scope =
      BuildConfigOverrideScope(parent_scope, config_localparam_scope_);

  for (const auto& ov : instance_param_overrides_) {
    if (ov.inst_path != current_inst_path_) continue;

    if (ov.reset_all) {
      ResetAllConfigParams(child_decl, child_params, locked);
    }
    ApplyConfigOverrideParams(ov.params, child_params, scope, locked);
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
  if (!item->inst_name.empty() &&
      !declared_names_.insert(ScopedName(item->inst_name)).second) {
    diag_.Error(item->loc,
                std::format("redeclaration of '{}'", item->inst_name),
                Subclause("23.9"));
  }
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;

  std::string saved_inst_path = current_inst_path_;
  if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
  current_inst_path_.append(item->inst_name.data(), item->inst_name.size());

  // §23.4: a name that resolves out of nested_module_decls_ names a module
  // declared inside this one, which sees this module's names.
  inst.is_nested_decl = nested_module_decls_.find(item->inst_module) !=
                        nested_module_decls_.end();
  auto* child_decl = FindModuleInScope(item->inst_module);
  if (!child_decl) {
    ReportUnknownModule(item, diag_);
    mod->children.push_back(inst);
    current_inst_path_ = std::move(saved_inst_path);
    return;
  }

  auto saved_nested = nested_module_decls_;
  Elaborator::ParamList child_params;
  auto parent_scope = BuildParamScope(mod);

  ResolveInstParams(item, child_decl, parent_scope, child_params, diag_);

  // A configuration may override (or reset) this instance's parameters on top
  // of whatever the instantiation specified (§33.4.3).
  std::vector<std::string_view> config_locked;
  ApplyConfigParamOverrides(child_decl, child_params, parent_scope,
                            config_locked);

  // §6.20.3/§23.10: publish the child's type-parameter substitutions into the
  // shared typedef map so its dependent declarations resolve against the chosen
  // types, then restore the map once the child has been elaborated.
  auto saved_type_params =
      ApplyChildTypeParams(item, child_decl, typedefs_, unit_, diag_);
  inst.resolved = ElaborateModule(child_decl, child_params);
  RestoreChildTypeParams(typedefs_, saved_type_params);
  nested_module_decls_ = std::move(saved_nested);

  MarkConfigLockedParams(inst, config_locked);
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

  CheckPortCoercion(inst, item->loc);
  CheckUwirePortMerge(inst, item, mod);
  CheckInterconnectPortMerge(inst, item, mod);

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
}

}  // namespace delta
