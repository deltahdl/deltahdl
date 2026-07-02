#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §6.20.3: convert a type-parameter override argument (which the expression
// parser produces as a plain identifier, e.g. `shortint` or a class name `C`)
// into a DataType, via the shared name->type mapping.
static DataType TypeParamOverrideToDataType(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kIdentifier) return DataType{};
  return TypeNameToDataType(expr->text);
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

// §6.20.3/§23.10: resolve each of the child's type parameters to a concrete
// type (an instantiation override if present, otherwise the declared default)
// and publish it in `typedefs` so the child's dependent declarations elaborate
// against the chosen type. A type parameter with neither a default nor an
// override is an error. Returns the prior entries so the caller can restore the
// shared map after the child is elaborated.
static std::vector<SavedTypedef> ApplyChildTypeParams(
    const ModuleItem* item, const ModuleDecl* child_decl, TypedefMap& typedefs,
    DiagEngine& diag) {
  std::vector<SavedTypedef> saved;
  for (size_t i = 0; i < child_decl->params.size(); ++i) {
    std::string_view pname = child_decl->params[i].first;
    if (child_decl->type_param_names.count(pname) == 0) continue;
    const Expr* ov = FindTypeParamOverrideExpr(item, child_decl, pname);
    bool has_default =
        i < child_decl->param_types.size() &&
        child_decl->param_types[i].kind != DataTypeKind::kImplicit;
    DataType resolved;
    if (ov && ov->kind == ExprKind::kIdentifier) {
      resolved = TypeParamOverrideToDataType(ov);
    } else if (has_default) {
      resolved = child_decl->param_types[i];
    } else {
      diag.Error(item->loc,
                 std::format("type parameter '{}' of '{}' has no default type "
                             "and no override at instantiation",
                             pname, child_decl->name));
      continue;
    }
    SavedTypedef s;
    s.name = pname;
    auto it = typedefs.find(pname);
    s.existed = it != typedefs.end();
    if (s.existed) s.prev = it->second;
    saved.push_back(s);
    typedefs[pname] = resolved;
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

static uint32_t EvalInstDimSize(const Expr* left, const Expr* right) {
  if (left && right) {
    auto lv = ConstEvalInt(left);
    auto rv = ConstEvalInt(right);
    if (lv && rv) return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  } else if (left) {
    auto v = ConstEvalInt(left);
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
                           targets.size()));
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
      diag.Error(item->loc, std::format("module '{}' has no parameter '{}'",
                                        item->inst_module, pname));
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
uint32_t ComputeInstDimSizes(const ModuleItem* item,
                             std::vector<uint32_t>& inst_dim_sizes) {
  uint32_t total_instances = 1;
  for (const auto& [left, right] : item->inst_dims) {
    uint32_t sz = EvalInstDimSize(left, right);
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
    diag.Error(item->loc,
               std::format("unknown module '{}'", item->inst_module));
  else
    diag.Error(item->loc, std::format("unknown module '{}::{}'",
                                      item->inst_scope, item->inst_module));
}

// Resolves the instantiation's own parameter overrides into child_params,
// dispatching on whether they were written positionally or by name.
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
// signal widths), and the parent's unpacked-array shapes.
struct InstArrayDistribCtx {
  Arena& arena;
  const RtlirModule* parent_mod;
  const VarArrayInfoMap& var_array_info;
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

// `base[lo +: width]` (ascending indexed part-select).
Expr* MakePartSelectPlusExpr(Arena& arena, Expr* base, uint32_t lo,
                             uint32_t width) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = MakeIntLitExpr(arena, lo);
  e->index_end = MakeIntLitExpr(arena, width);
  e->is_part_select_plus = true;
  return e;
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
      return MakePartSelectPlusExpr(ctx.arena, conn, position * port_width,
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
    return MakePartSelectPlusExpr(ctx.arena, conn, position * port_width,
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
                             const ModuleItem* item) {
  std::optional<int64_t> arr_left;
  std::optional<int64_t> arr_right;
  if (item->inst_dims.size() == 1) {
    if (item->inst_range_left) arr_left = ConstEvalInt(item->inst_range_left);
    if (item->inst_range_right)
      arr_right = ConstEvalInt(item->inst_range_right);
  }
  if (arr_left && arr_right) {
    PushInstanceArray(ctx, mod, inst, *arr_left, *arr_right);
  } else {
    mod->children.push_back(inst);
  }
}

}  // namespace

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
  if (!item->inst_name.empty() &&
      !declared_names_.insert(item->inst_name).second) {
    diag_.Error(item->loc,
                std::format("redeclaration of '{}'", item->inst_name));
  }
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;

  std::string saved_inst_path = current_inst_path_;
  if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
  current_inst_path_.append(item->inst_name.data(), item->inst_name.size());

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
      ApplyChildTypeParams(item, child_decl, typedefs_, diag_);
  inst.resolved = ElaborateModule(child_decl, child_params);
  RestoreChildTypeParams(typedefs_, saved_type_params);
  nested_module_decls_ = std::move(saved_nested);

  MarkConfigLockedParams(inst, config_locked);
  BindPorts(inst, item, mod, child_decl);

  std::vector<uint32_t> inst_dim_sizes;
  uint32_t total_instances = ComputeInstDimSizes(item, inst_dim_sizes);

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
      (!ConstEvalInt(item->inst_range_left) ||
       !ConstEvalInt(item->inst_range_right))) {
    diag_.Error(item->loc,
                "instance array range bound must be a constant expression");
  }
  InstArrayDistribCtx dctx{arena_, mod, var_array_info_};
  AppendModuleInstOrArray(dctx, mod, inst, item);
  current_inst_path_ = std::move(saved_inst_path);
}

}  // namespace delta
