#include <cstddef>
#include <optional>
#include <set>
#include <string_view>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

// Reads `expr` into the steps of §23.6's Syntax 23-7, folding each instance
// select against `scope`. Returns false when the expression is not a path at
// all, or when a select does not fold: §23.6 rules that the select "shall
// evaluate to one of the legal index values of the array", so one that does not
// names no instance and the caller reports the path as reaching nothing.
//
// The select is folded here rather than at the point of comparison because a
// defparam standing in a loop generate block may write its own genvar --
// §23.10.1's example is `defparam somename[i+1].my_flop.xyz = i` -- and `scope`
// carries that binding only while the block instance is being applied.
static bool CollectPathSteps(const Expr* expr, const ScopeMap& scope,
                             HierPath& out) {
  if (expr->kind == ExprKind::kMemberAccess) {
    if (!CollectPathSteps(expr->lhs, scope, out)) return false;
    out.push_back({expr->rhs->text, false, 0});
    return true;
  }
  if (expr->kind == ExprKind::kSelect) {
    if (!CollectPathSteps(expr->base, scope, out)) return false;
    if (out.empty()) return false;
    auto index = ConstEvalInt(expr->index, scope);
    if (!index) return false;
    out.back().has_index = true;
    out.back().index = *index;
    return true;
  }
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back({expr->text, false, 0});
    return true;
  }
  return false;
}

static bool RhsContainsHierarchicalRef(const Expr* e);

// True if any scalar (single-Expr) child slot of `e` contains a hierarchical
// reference. Kept separate so the top-level node check stays simple.
static bool AnyScalarChildContainsHierarchicalRef(const Expr* e) {
  return RhsContainsHierarchicalRef(e->lhs) ||
         RhsContainsHierarchicalRef(e->rhs) ||
         RhsContainsHierarchicalRef(e->base) ||
         RhsContainsHierarchicalRef(e->index) ||
         RhsContainsHierarchicalRef(e->index_end) ||
         RhsContainsHierarchicalRef(e->condition) ||
         RhsContainsHierarchicalRef(e->true_expr) ||
         RhsContainsHierarchicalRef(e->false_expr) ||
         RhsContainsHierarchicalRef(e->repeat_count);
}

// True if any element of one of `e`'s child-Expr lists contains a hierarchical
// reference.
static bool AnyListChildContainsHierarchicalRef(const Expr* e) {
  for (const auto* a : e->args) {
    if (RhsContainsHierarchicalRef(a)) return true;
  }
  for (const auto* elem : e->elements) {
    if (RhsContainsHierarchicalRef(elem)) return true;
  }
  return false;
}

static bool RhsContainsHierarchicalRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty()) return true;
  if (AnyScalarChildContainsHierarchicalRef(e)) return true;
  return AnyListChildContainsHierarchicalRef(e);
}

// True when a step of a path a source wrote names the same generate block
// instance a step recorded on a declaration does.
static bool SameHierStep(const HierStep& written, const HierStep& recorded) {
  if (written.name != recorded.name) return false;
  if (written.has_index != recorded.has_index) return false;
  return !written.has_index || written.index == recorded.index;
}

// The module `mod` instantiates as `name` inside exactly the generate block
// instances `blocks` names, or nullptr when it instantiates no such thing.
static RtlirModule* ChildUnderBlocks(RtlirModule* mod, std::string_view name,
                                     const HierPath& blocks) {
  for (auto& child : mod->children) {
    if (!child.resolved) continue;
    if (child.simple_inst_name != name) continue;
    if (child.gen_block_path.size() != blocks.size()) continue;
    bool same = true;
    for (size_t i = 0; i < blocks.size(); ++i) {
      if (!SameHierStep(blocks[i], child.gen_block_path[i])) {
        same = false;
        break;
      }
    }
    if (same) return child.resolved;
  }
  return nullptr;
}

// Follows every step of `path` but the last down the instance hierarchy from
// `root`, starting inside the generate block instances `writer` names. Returns
// the module the last step is declared in, or nullptr when no such module was
// elaborated.
//
// A step names a generate block instance or a module instance, and §23.6 makes
// it exactly one of the two: "each node in the hierarchical name tree shall be
// a separate scope with respect to identifiers", and a module holds its blocks
// and its instances in one scope, so no step can name both. Reading a step as
// an instance first is therefore a decision rather than a guess, and a step
// that names no instance is a block: it is remembered and the instance it
// qualifies is looked for one step further on.
//
// A step carrying an instance select is never read as an instance. §23.6 admits
// one over an instance array as well as over a loop generate block, but nothing
// records which element of an array a child is, so such a step would match
// every element alike.
static RtlirModule* DescendDefparamPath(RtlirModule* root, const HierPath& path,
                                        const HierPath& writer) {
  RtlirModule* cur = root;
  HierPath blocks = writer;
  for (size_t i = 0; i + 1 < path.size(); ++i) {
    RtlirModule* next = path[i].has_index
                            ? nullptr
                            : ChildUnderBlocks(cur, path[i].name, blocks);
    if (next != nullptr) {
      cur = next;
      blocks.clear();
      continue;
    }
    blocks.push_back(path[i]);
  }
  // Leftover steps named generate block instances that nothing was instantiated
  // in, so the path reached a scope rather than a module and names no
  // parameter.
  return blocks.empty() ? cur : nullptr;
}

RtlirParamDecl* Elaborator::ResolveDefparamSteps(RtlirModule* root,
                                                 const HierPath& path,
                                                 const HierPath& writer,
                                                 RtlirModule** out_mod) {
  if (path.size() < 2) return nullptr;

  RtlirModule* cur = DescendDefparamPath(root, path, writer);
  if (!cur) return nullptr;

  auto param_name = path.back().name;
  for (auto& p : cur->params) {
    if (p.name == param_name) {
      if (out_mod) *out_mod = cur;
      return &p;
    }
  }
  return nullptr;
}

void Elaborator::RecomputeDependentParams(RtlirModule* mod) {
  if (!mod) return;
  for (auto& p : mod->params) {
    if (p.from_override) continue;
    if (p.is_type_param) continue;
    if (p.is_unbounded) continue;
    if (!p.default_value) continue;
    auto scope = BuildParamScope(mod);
    auto val = ConstEvalInt(p.default_value, scope);
    if (val) {
      p.resolved_value = *val;
      p.is_resolved = true;
    }
  }
}

// Checks whether a defparam may legally override the resolved target `param`
// whose right-hand side is `val_expr`. On a violation it emits the matching
// diagnostic against `loc` and returns false (the caller then records the
// defparam as handled and skips it). Returns true when the override may
// proceed.
static bool DefparamOverrideAllowed(DiagEngine& diag,
                                    const RtlirParamDecl* param,
                                    const Expr* val_expr, SourceLoc loc) {
  if (param->is_type_param) {
    diag.Error(loc, "defparam cannot override a type parameter",
               Subclause("23.10.1"));
    return false;
  }
  if (param->is_localparam) {
    diag.Error(loc, "defparam cannot override a local parameter",
               Subclause("23.10.1"));
    return false;
  }
  if (param->config_locked) {
    // A configuration's parameter override takes precedence over a defparam
    // targeting the same parameter (§33.4.3); leave the config value in
    // place and treat this defparam as resolved against it.
    return false;
  }
  if (RhsContainsHierarchicalRef(val_expr)) {
    diag.Error(loc,
               "defparam right-hand side may only reference parameters "
               "declared in the same module",
               Subclause("23.10.1"));
    return false;
  }
  return true;
}

// One defparam override as an LRM entity (§23.10.4): the resolved target
// parameter, the right-hand side value expression, the scope its value is
// evaluated in, and the source location of the defparam statement.
struct DefparamOverride {
  const RtlirParamDecl* param;
  const Expr* val_expr;
  const ScopeMap& scope;
  SourceLoc loc;
};

// The bookkeeping for which defparam assignments have been handled: the
// applied-set keyed by (module, item, assignment index) plus the key naming
// this particular assignment.
using DefparamAppliedKey =
    std::tuple<RtlirModule*, const ModuleItem*, size_t, std::string_view>;
struct DefparamAppliedRecord {
  std::set<DefparamAppliedKey>& applied;
  const DefparamAppliedKey& key;
};

// Validates one already-resolved defparam target and, if the override may
// proceed, evaluates its right-hand side. On any rejection (illegal override or
// non-constant value) the assignment key is recorded in the applied set and an
// empty optional is returned; the caller then skips it. On success the
// converted override value is returned.
static std::optional<int64_t> EvalDefparamOverride(
    DiagEngine& diag, const DefparamOverride& ovr,
    const DefparamAppliedRecord& rec) {
  if (!DefparamOverrideAllowed(diag, ovr.param, ovr.val_expr, ovr.loc)) {
    rec.applied.insert(rec.key);
    return std::nullopt;
  }
  auto val = ConstEvalInt(ovr.val_expr, ovr.scope);
  if (!val) {
    // §23.10.1 states that the expression on the right-hand side of a defparam
    // assignment shall be a constant expression involving only numbers and
    // references to parameters. A right-hand side that is no constant
    // expression breaks that rule, so the source is illegal and the report is
    // an error. Folding can also fail on a right-hand side that is a constant
    // expression, which breaks no rule and stays the warning it was.
    if (!IsConstantExpr(ovr.val_expr, ovr.scope)) {
      diag.Error(ovr.loc,
                 "defparam right-hand side shall be a constant expression "
                 "involving only numbers and references to parameters",
                 Subclause("23.10.1"));
    } else {
      diag.Warning(ovr.loc, "defparam value is not constant",
                   Subclause("23.10.1"));
    }
    rec.applied.insert(rec.key);
    return std::nullopt;
  }
  return ConvertOverrideValue(*val, *ovr.param);
}

// §6.16: a defparam replaces the whole of the parameter's value, and for one
// declared string that value is characters rather than the §11.10 packed number
// resolved_value holds. Elaborator::ElaborateParamDecl has already recorded the
// declaration's own characters by the time a defparam lands, so they are
// replaced here or the value the defparam overrode is what Lowerer::LowerParams
// reads. Clearing is_string_value where the right-hand side is not a string
// literal is what sends the lowering to resolved_value, which
// EvalDefparamOverride did write, in preference to characters that are no
// longer the parameter's. Does nothing for a parameter that never held a string
// value.
static void ReplaceStringParamValue(RtlirParamDecl& pd, const Expr* val_expr,
                                    Arena& arena) {
  if (!pd.is_string_value) return;
  if (!RecordStringParamChars(pd, val_expr, arena)) pd.is_string_value = false;
}

// Trailing return type: DefparamSite is a protected member of ElaboratorData,
// which the class scope opened by the Elaborator:: qualifier reaches and
// namespace scope does not.
auto Elaborator::CollectDefparamSites(RtlirModule* mod,
                                      const ModuleDecl* decl) const
    -> std::vector<DefparamSite> {
  std::vector<DefparamSite> sites;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    sites.push_back({item, {}, {}, {}});
  }
  auto it = generate_defparams_.find(mod);
  if (it != generate_defparams_.end())
    sites.insert(sites.end(), it->second.begin(), it->second.end());
  return sites;
}

void Elaborator::ApplyDefparamSite(RtlirModule* mod, const DefparamSite& site,
                                   const ScopeMap& scope) {
  for (size_t idx = 0; idx < site.item->defparam_assigns.size(); ++idx) {
    auto key = std::make_tuple(mod, site.item, idx, site.prefix);
    if (applied_defparams_.count(key)) continue;
    const auto& [path_expr, val_expr] = site.item->defparam_assigns[idx];
    HierPath path;
    if (!CollectPathSteps(path_expr, scope, path)) continue;
    RtlirModule* target_mod = nullptr;
    auto* param = ResolveDefparamSteps(mod, path, site.path, &target_mod);
    if (!param) continue;
    DefparamOverride ovr{param, val_expr, scope, site.item->loc};
    DefparamAppliedRecord rec{applied_defparams_, key};
    auto value = EvalDefparamOverride(diag_, ovr, rec);
    if (!value) continue;

    param->resolved_value = *value;
    param->is_resolved = true;
    param->from_override = true;
    ReplaceStringParamValue(*param, val_expr, arena_);
    RecomputeDependentParams(target_mod);
    applied_defparams_.insert(key);
    early_defparam_resolutions_.push_back(
        {mod, path, site.path, param, site.item->loc});
  }
}

void Elaborator::ApplyDefparams(RtlirModule* mod, const ModuleDecl* decl) {
  // §6.16: a defparam's right-hand side is written in the module holding the
  // defparam statement, so that module's parameters are what a name in it
  // means, and registering it is what lets ConstEvalString read the characters
  // of one. ApplyDefparamsRecursively runs outside every module, so without
  // this no module is registered and a defparam naming a string parameter
  // recovers nothing.
  ParamRangeRegistryGuard param_range_guard(mod);
  ScopeMap mod_scope = BuildParamScope(mod);
  for (const auto& site : CollectDefparamSites(mod, decl)) {
    // §27.4 opens a localparam sharing the loop index's name in each instance
    // of a loop generate block, and §23.10.1's own example reads it on a
    // right-hand side. The module's parameters are rebuilt on every pass
    // because an earlier defparam may have changed one, so the block's bindings
    // are laid over that rather than kept in place of it.
    ScopeMap scope = mod_scope;
    for (const auto& [name, value] : site.consts) scope[name] = value;
    ApplyDefparamSite(mod, site, scope);
  }
}

void Elaborator::VerifyEarlyResolvedDefparams() {
  for (const auto& rec : early_defparam_resolutions_) {
    auto* now = ResolveDefparamSteps(rec.root, rec.path, rec.writer_path);
    if (now != nullptr && now != rec.resolved) {
      diag_.Error(rec.loc,
                  "defparam hierarchical name resolves differently after "
                  "full elaboration than during early resolution",
                  Subclause("23.10.4.2"));
    }
  }
}

// Names of the generate blocks a conditional/loop generate construct can
// introduce directly into the enclosing scope. A conditional construct
// contributes its then-block name plus, recursively, the names of every
// else/else-if alternative; a case construct contributes each item label; a
// loop construct contributes its array name.
static void CollectLocalGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      if (!item->name.empty()) out.insert(item->name);
      if (item->gen_else) CollectLocalGenerateBlockNames(item->gen_else, out);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items)
        if (!ci.label.empty()) out.insert(ci.label);
      break;
    case ModuleItemKind::kGenerateFor:
      if (!item->name.empty()) out.insert(item->name);
      break;
    default:
      break;
  }
}

// §23.10.4.2: a defparam's hierarchical name may have to be resolved before the
// hierarchy is fully elaborated (so a generate condition that reads the target
// can be evaluated). If that early resolution would differ from the resolution
// the completed hierarchy dictates, it is an error. The situation arises when a
// named generate block in the module holding the defparam shares its name with
// a scope named by the leading component of the defparam's path: before the
// block is elaborated the leading name resolves outward (here, to a top-level
// module of the same name), but once the block exists the same name would bind
// to the local block instead, changing the target. We flag that collision; per
// the LRM it is fixed by renaming the generate block.
// Flags each defparam assignment in `item` whose leading path component names
// both a local generate block and a top-level scope: that name resolves
// outward now but would bind to the local block once it is elaborated.
static void CheckDefparamItemEarlyAmbiguity(
    DiagEngine& diag, const ModuleItem* item,
    const std::unordered_set<std::string_view>& block_names,
    const std::unordered_set<std::string_view>& top_names) {
  for (const auto& assign : item->defparam_assigns) {
    HierPath parts;
    if (!CollectPathSteps(assign.first, {}, parts)) continue;
    if (parts.size() < 2) continue;
    auto lead = parts.front().name;
    if (block_names.count(lead) && top_names.count(lead)) {
      diag.Error(item->loc,
                 "defparam hierarchical name would resolve differently once "
                 "the like-named generate block is elaborated",
                 Subclause("23.10.4.2"));
    }
  }
}

void Elaborator::CheckEarlyResolutionAmbiguity(
    RtlirModule* mod, const std::unordered_set<std::string_view>& top_names) {
  if (!mod) return;
  const auto* decl = FindModule(mod->name);
  if (!decl) return;

  std::unordered_set<std::string_view> block_names;
  for (const auto* item : decl->items)
    CollectLocalGenerateBlockNames(item, block_names);
  if (block_names.empty()) return;

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    CheckDefparamItemEarlyAmbiguity(diag_, item, block_names, top_names);
  }
}

void Elaborator::ApplyDefparamsRecursively(RtlirModule* mod) {
  if (!mod) return;
  if (auto* decl = FindModule(mod->name)) {
    ApplyDefparams(mod, decl);
  }
  for (auto& child : mod->children) {
    ApplyDefparamsRecursively(child.resolved);
  }
}

// Reports every assignment of one defparam statement that was never applied.
// §23.10.1 gives two reasons for that and they are different diagnoses. A
// statement inside a generate block whose target exists but lies outside the
// block breaks the clause's rule that such a statement "shall not change a
// parameter value outside that hierarchy", and is an error. Anything else named
// nothing at all, and stays the warning it was.
void Elaborator::ReportUnresolvedDefparamSite(RtlirModule* mod,
                                              const DefparamSite& site,
                                              const ScopeMap& mod_scope) {
  ScopeMap scope = mod_scope;
  for (const auto& [name, value] : site.consts) scope[name] = value;
  for (size_t idx = 0; idx < site.item->defparam_assigns.size(); ++idx) {
    auto key = std::make_tuple(mod, site.item, idx, site.prefix);
    if (applied_defparams_.count(key)) continue;
    const Expr* path_expr = site.item->defparam_assigns[idx].first;
    HierPath path;
    bool read = CollectPathSteps(path_expr, scope, path);
    if (!site.path.empty() && read &&
        ResolveDefparamSteps(mod, path, {}) != nullptr) {
      diag_.Error(site.item->loc,
                  "defparam in a generate block shall not change a parameter "
                  "value outside that block",
                  Subclause("23.10.1"));
      continue;
    }
    diag_.Warning(site.item->loc, "defparam target not found",
                  Subclause("23.10.1"));
  }
}

void Elaborator::ReportUnresolvedDefparams(RtlirModule* mod,
                                           const ModuleDecl* decl) {
  ParamRangeRegistryGuard param_range_guard(mod);
  ScopeMap mod_scope = BuildParamScope(mod);
  for (const auto& site : CollectDefparamSites(mod, decl)) {
    ReportUnresolvedDefparamSite(mod, site, mod_scope);
  }
}

void Elaborator::WarnUnresolvedDefparams(RtlirModule* mod) {
  if (!mod) return;
  if (auto* decl = FindModule(mod->name)) {
    ReportUnresolvedDefparams(mod, decl);
  }
  for (auto& child : mod->children) {
    WarnUnresolvedDefparams(child.resolved);
  }
}

}  // namespace delta
