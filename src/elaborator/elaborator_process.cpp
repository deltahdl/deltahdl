#include <algorithm>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_process_validate.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

RtlirNet MakeImplicitPortNet(std::string_view name, uint32_t port_width,
                             bool port_is_signed, NetType default_nettype) {
  RtlirNet net;
  net.name = name;
  net.net_type = default_nettype;
  net.width = port_width == 0 ? 1 : port_width;
  net.is_signed = port_is_signed;
  return net;
}

uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod) {
  std::string_view name = LhsSignalName(lhs);
  if (name.empty()) return 0;
  return LookupNameWidth(name, mod);
}

uint32_t LookupNameWidth(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  return 0;
}

RtlirProcessKind MapAlwaysKind(AlwaysKind ak) {
  switch (ak) {
    case AlwaysKind::kAlways:
      return RtlirProcessKind::kAlways;
    case AlwaysKind::kAlwaysComb:
      return RtlirProcessKind::kAlwaysComb;
    case AlwaysKind::kAlwaysFF:
      return RtlirProcessKind::kAlwaysFF;
    case AlwaysKind::kAlwaysLatch:
      return RtlirProcessKind::kAlwaysLatch;
  }
  return RtlirProcessKind::kAlwaysComb;
}

static Stmt* BuildProcessBody(const ModuleItem* item,
                              const ProcessBuildEnv& env) {
  if (env.global_clocking_event == nullptr) return item->body;
  return SubstituteGlobalClockEventControls(
      item->body, *env.global_clocking_event, env.arena);
}

static RtlirProcess BuildProcessWithSensitivity(RtlirProcessKind kind,
                                                ModuleItem* item,
                                                const ProcessBuildEnv& env) {
  RtlirProcess proc;
  proc.kind = kind;
  proc.loc = item->loc;
  proc.body = BuildProcessBody(item, env);
  proc.sensitivity = item->sensitivity;
  if (env.global_clocking_event != nullptr) {
    SubstituteGlobalClockLeadingEvent(proc.sensitivity,
                                      *env.global_clocking_event);
  }
  proc.is_star_sensitivity = item->is_star_sensitivity;
  bool needs_infer = (kind == RtlirProcessKind::kAlwaysComb ||
                      kind == RtlirProcessKind::kAlwaysLatch);
  if (needs_infer && proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, env.arena, env.func_map,
                                        true, env.const_names);
  }
  if (kind == RtlirProcessKind::kAlways && item->is_star_sensitivity &&
      proc.sensitivity.empty()) {
    proc.sensitivity =
        InferSensitivity(proc.body, env.arena, nullptr, false, env.const_names);
  }
  return proc;
}

void AddProcess(RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod,
                const ProcessBuildEnv& env, const ScopeMap& params) {
  RtlirProcess proc = BuildProcessWithSensitivity(kind, item, env);
  static const std::unordered_set<std::string> kNoTasks;
  ValidateProcess(kind, item, proc, env.diag,
                  env.task_names != nullptr ? *env.task_names : kNoTasks);
  proc.attrs = ResolveAttributes(item->attrs, env.diag, params);
  mod->processes.push_back(proc);
}

void AddStaticAssertionProcess(RtlirProcessKind kind, ModuleItem* item,
                               RtlirModule* mod, const ProcessBuildEnv& env) {
  RtlirProcess proc = BuildProcessWithSensitivity(kind, item, env);
  ValidateProcess(kind, item, proc, env.diag, {});
  proc.is_static_assertion = true;
  mod->processes.push_back(proc);
}

static size_t PushForHeaderLocals(const Stmt* stmt,
                                  std::vector<std::string_view>& locals) {
  if (stmt->kind != StmtKind::kFor) return 0;
  size_t pushed = 0;
  for (size_t k = 0;
       k < stmt->for_inits.size() && k < stmt->for_init_types.size(); ++k) {
    const Stmt* init = stmt->for_inits[k];
    if (stmt->for_init_types[k].kind == DataTypeKind::kImplicit) continue;
    if (init == nullptr || init->lhs == nullptr) continue;
    locals.push_back(init->lhs->text);
    ++pushed;
  }
  return pushed;
}

static size_t PushBlockLocals(const Stmt* stmt,
                              std::vector<std::string_view>& locals) {
  if (stmt->kind != StmtKind::kBlock && stmt->kind != StmtKind::kFork) return 0;
  size_t pushed = 0;
  for (const auto* item : stmt->stmts) {
    if (item == nullptr || item->kind != StmtKind::kVarDecl) continue;
    locals.push_back(item->var_name);
    ++pushed;
  }
  return pushed;
}

static bool IsDeclaredLocal(std::string_view prefix,
                            const std::vector<std::string_view>& locals) {
  std::string_view base = prefix.substr(0, prefix.find_first_of(".["));
  return std::ranges::find(locals, base) != locals.end();
}

static void CollectLhsPrefixesInScope(const Stmt* stmt,
                                      std::unordered_set<std::string>& out,
                                      const ScopeMap& scope,
                                      std::vector<std::string_view>& locals) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign ||
      stmt->kind == StmtKind::kAssign) {
    if (stmt->lhs) {
      std::string prefix = LongestStaticPrefix(stmt->lhs, scope);
      if (!prefix.empty() && !IsDeclaredLocal(prefix, locals))
        out.insert(std::move(prefix));
    }
  }
  size_t pushed = PushForHeaderLocals(stmt, locals);
  pushed += PushBlockLocals(stmt, locals);
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    CollectLhsPrefixesInScope(sub, out, scope, locals);
  });
  locals.resize(locals.size() - pushed);
}

static void CollectStmtLhsPrefixes(const Stmt* stmt,
                                   std::unordered_set<std::string>& out,
                                   const ScopeMap& scope) {
  std::vector<std::string_view> locals;
  CollectLhsPrefixesInScope(stmt, out, scope, locals);
}

static void CollectCallNamesExpr(const Expr* expr,
                                 std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    out.insert(expr->callee);
  ForEachExprChild(
      expr, [&](const Expr* child) { CollectCallNamesExpr(child, out); });
}

static void CollectCallNamesStmt(const Stmt* stmt,
                                 std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  ForEachChildExpr(stmt, [&](Expr* const& e) { CollectCallNamesExpr(e, out); });
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CollectCallNamesStmt(sub, out); });
}

static std::vector<std::string_view> FunctionOwnNames(const ModuleItem& func) {
  std::vector<std::string_view> names{func.name};
  for (const FunctionArg& arg : func.func_args) names.push_back(arg.name);
  for (const Stmt* s : func.func_body_stmts) {
    if (s->kind == StmtKind::kVarDecl) names.push_back(s->var_name);
  }
  return names;
}

static void CollectFuncLhsPrefixes(const Stmt* body, const FuncMap& funcs,
                                   std::unordered_set<std::string>& out,
                                   const ScopeMap& scope) {
  std::unordered_set<std::string_view> pending;
  CollectCallNamesStmt(body, pending);
  std::unordered_set<std::string_view> visited;
  while (!pending.empty()) {
    std::unordered_set<std::string_view> next;
    for (auto& name : pending) {
      if (visited.count(name)) continue;
      visited.insert(name);
      auto it = funcs.find(name);
      if (it == funcs.end()) continue;
      std::vector<std::string_view> locals = FunctionOwnNames(*it->second);
      for (auto* s : it->second->func_body_stmts) {
        CollectLhsPrefixesInScope(s, out, scope, locals);
        CollectCallNamesStmt(s, next);
      }
    }
    pending = std::move(next);
  }
}

static void CollectProcedureLhsPrefixes(const Stmt* body,
                                        const FuncMap* func_map,
                                        std::unordered_set<std::string>& out,
                                        const ScopeMap& scope) {
  CollectStmtLhsPrefixes(body, out, scope);
  if (func_map && !func_map->empty())
    CollectFuncLhsPrefixes(body, *func_map, out, scope);
}

struct TrailingSelect {
  std::string_view base;
  int64_t low;
  int64_t high;
};

static std::optional<TrailingSelect> SplitTrailingSelect(std::string_view p) {
  const size_t kOpen = p.rfind('[');
  if (kOpen == std::string_view::npos || p.back() != ']') return std::nullopt;
  const char* begin = p.data() + kOpen + 1;
  const char* end = p.data() + p.size() - 1;
  TrailingSelect sel{p.substr(0, kOpen), 0, 0};
  const std::from_chars_result kLow = std::from_chars(begin, end, sel.low);
  sel.high = sel.low;
  if (kLow.ptr != end) {
    const std::from_chars_result kHigh =
        std::from_chars(kLow.ptr + 1, end, sel.high);
    static_cast<void>(kHigh);
  }
  return sel;
}

static bool PrefixesOverlap(const std::string& a, const std::string& b) {
  if (a == b) return true;
  auto sa = SplitTrailingSelect(a);
  auto sb = SplitTrailingSelect(b);
  if (sa && sb && sa->base == sb->base)
    return sa->low <= sb->high && sb->low <= sa->high;
  if (a.size() < b.size())
    return b.compare(0, a.size(), a) == 0 &&
           (b[a.size()] == '.' || b[a.size()] == '[');
  if (b.size() < a.size())
    return a.compare(0, b.size(), b) == 0 &&
           (a[b.size()] == '.' || a[b.size()] == '[');
  return false;
}

struct ProcInfo {
  SourceLoc loc;
  std::unordered_set<std::string> lhs;
  ModuleItemKind kind;
};

struct ProcessDriverSets {
  std::vector<ProcInfo>& procs;
  std::unordered_set<std::string>& cont_assign_lhs;
  std::unordered_set<std::string>& general_proc_lhs;
};

static const char* ProcessKindLabel(ModuleItemKind k) {
  switch (k) {
    case ModuleItemKind::kAlwaysFFBlock:
      return "always_ff";
    case ModuleItemKind::kAlwaysLatchBlock:
      return "always_latch";
    default:
      return "always_comb";
  }
}

static ProcInfo MakeProcInfo(const ModuleItem* item, const FuncMap* func_map,
                             const ScopeMap& scope) {
  ProcInfo info;
  info.loc = item->loc;
  info.kind = item->kind;
  CollectProcedureLhsPrefixes(item->body, func_map, info.lhs, scope);
  return info;
}

static std::vector<const Expr*> ContinuousTargets(const ModuleItem* item) {
  if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs)
    return {item->assign_lhs};
  if (item->kind != ModuleItemKind::kGateInst &&
      item->kind != ModuleItemKind::kUdpInst)
    return {};
  std::span<Expr* const> outputs = PrimitiveOutputTerminals(item);
  return {outputs.begin(), outputs.end()};
}

static void CollectProcessLhsInfo(const ModuleDecl* decl,
                                  const ProcessDriverSets& drivers,
                                  const FuncMap* func_map,
                                  const ScopeMap& scope) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock) {
      drivers.procs.push_back(MakeProcInfo(item, func_map, scope));
    }
    for (const Expr* target : ContinuousTargets(item)) {
      std::string prefix = LongestStaticPrefix(target, scope);
      if (!prefix.empty()) drivers.cont_assign_lhs.insert(std::move(prefix));
    }
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      CollectProcedureLhsPrefixes(item->body, func_map,
                                  drivers.general_proc_lhs, scope);
    }
  }
}

static void CheckMultiProcDriver(const std::string& prefix, size_t i,
                                 const std::vector<ProcInfo>& procs,
                                 DiagEngine& diag) {
  for (size_t j = i + 1; j < procs.size(); ++j) {
    for (const auto& other : procs[j].lhs) {
      if (PrefixesOverlap(prefix, other)) {
        diag.Error(procs[j].loc,
                   std::format("variable '{}' driven by multiple "
                               "always_comb/always_latch/always_ff "
                               "processes",
                               prefix),
                   Subclause("9.2.2.2"));
        break;
      }
    }
  }
}

static void CheckContAssignConflict(
    const std::string& var, const ProcInfo& proc,
    const std::unordered_set<std::string>& cont_assign_lhs, DiagEngine& diag) {
  for (const auto& ca : cont_assign_lhs) {
    if (PrefixesOverlap(var, ca)) {
      diag.Error(proc.loc,
                 std::format("variable '{}' driven by {} and "
                             "continuous assignment",
                             var, ProcessKindLabel(proc.kind)),
                 Subclause("10.3.2"));
      break;
    }
  }
}

static void CheckGeneralProcOverlap(
    const std::string& var, const ProcInfo& proc,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (const auto& other : general_proc_lhs) {
    if (PrefixesOverlap(var, other)) {
      diag.Error(
          proc.loc,
          std::format("variable '{}' driven by {} and "
                      "another process",
                      var, ProcessKindLabel(proc.kind)),
          Subclause(proc.kind == ModuleItemKind::kAlwaysFFBlock ? "9.2.2.4"
                                                                : "9.2.2.2"));
      return;
    }
  }
}

static void CheckGeneralProcConflict(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (const auto& proc : procs) {
    for (const auto& var : proc.lhs)
      CheckGeneralProcOverlap(var, proc, general_proc_lhs, diag);
  }
}

static void CheckDriverConflicts(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& cont_assign_lhs,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (size_t i = 0; i < procs.size(); ++i) {
    for (const auto& var : procs[i].lhs) {
      CheckContAssignConflict(var, procs[i], cont_assign_lhs, diag);
      CheckMultiProcDriver(var, i, procs, diag);
    }
  }
  CheckGeneralProcConflict(procs, general_proc_lhs, diag);
}

void Elaborator::CheckAlwaysCombMultiDriver(const ModuleDecl* decl,
                                            RtlirModule* mod) {
  std::vector<ProcInfo> procs;
  std::unordered_set<std::string> cont_assign_lhs;
  std::unordered_set<std::string> general_proc_lhs;
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  CollectProcessLhsInfo(decl, {procs, cont_assign_lhs, general_proc_lhs},
                        &func_decls_, scope);
  CheckDriverConflicts(procs, cont_assign_lhs, general_proc_lhs, diag_);
}

struct ContTarget {
  std::string prefix;
  bool aggregate;
  SourceLoc loc;
};

static void CollectAggregateDriverTargets(
    const ModuleDecl* decl, const ScopeMap& scope,
    const std::unordered_set<std::string>& nets, std::vector<ContTarget>& conts,
    std::unordered_set<std::string>& proc_prefixes) {
  for (const auto* item : decl->items) {
    for (const Expr* target : ContinuousTargets(item)) {
      std::string prefix = LongestStaticPrefix(target, scope);
      if (prefix.empty() ||
          nets.contains(prefix.substr(0, prefix.find_first_of(".[")))) {
        continue;
      }
      bool aggregate = prefix.find('.') != std::string::npos ||
                       prefix.find('[') != std::string::npos;
      conts.push_back({std::move(prefix), aggregate, item->loc});
    }
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      CollectStmtLhsPrefixes(item->body, proc_prefixes, scope);
    }
  }
}

static void CheckOverlappingContTargets(const std::vector<ContTarget>& conts,
                                        DiagEngine& diag) {
  for (size_t i = 0; i < conts.size(); ++i) {
    for (size_t j = i + 1; j < conts.size(); ++j) {
      if (!conts[i].aggregate && !conts[j].aggregate) continue;
      if (PrefixesOverlap(conts[i].prefix, conts[j].prefix)) {
        diag.Error(conts[j].loc,
                   std::format("multiple continuous assignments drive "
                               "overlapping element '{}'",
                               conts[j].prefix),
                   Subclause("6.5"));
      }
    }
  }
}

static void CheckContProcElementMix(
    const std::vector<ContTarget>& conts,
    const std::unordered_set<std::string>& proc_prefixes, DiagEngine& diag) {
  for (const auto& ct : conts) {
    if (!ct.aggregate) continue;
    for (const auto& pp : proc_prefixes) {
      if (PrefixesOverlap(ct.prefix, pp)) {
        diag.Error(ct.loc,
                   std::format("element '{}' has both a continuous assignment "
                               "and a procedural assignment",
                               ct.prefix),
                   Subclause("10.3.2"));
        break;
      }
    }
  }
}

void Elaborator::CheckAggregateElementDrivers(const ModuleDecl* decl,
                                              RtlirModule* mod) {
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  std::vector<ContTarget> conts;
  std::unordered_set<std::string> proc_prefixes;
  std::unordered_set<std::string> nets;
  if (mod != nullptr) {
    for (const auto& net : mod->nets) nets.emplace(net.name);
    for (const auto& port : mod->ports) {
      if (port.net_type != NetType::kNone) nets.emplace(port.name);
    }
  }
  CollectAggregateDriverTargets(decl, scope, nets, conts, proc_prefixes);
  CheckOverlappingContTargets(conts, diag_);
  CheckContProcElementMix(conts, proc_prefixes, diag_);
}

}  // namespace delta
