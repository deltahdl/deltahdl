#include <format>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"

namespace delta {

RtlirNet MakeImplicitPortNet(std::string_view name, uint32_t port_width,
                             bool port_is_signed, NetType default_nettype) {
  RtlirNet net;
  net.name = name;
  // §6.10: an implicit net assumed for a port expression takes the default net
  // type and the vector width of the port expression declaration.
  net.net_type = default_nettype;
  net.width = port_width == 0 ? 1 : port_width;
  // §23.2.2.1: nets connected to ports without an explicit net declaration are
  // unsigned unless the port itself is declared signed.
  net.is_signed = port_is_signed;
  return net;
}

uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier) return 0;
  for (const auto& v : mod->variables) {
    if (v.name == lhs->text) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == lhs->text) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == lhs->text) return p.width;
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

static bool StmtHasForkJoin(const Stmt* stmt) {
  if (!stmt) return false;
  if (stmt->kind == StmtKind::kFork) return true;
  for (const auto* s : stmt->stmts)
    if (StmtHasForkJoin(s)) return true;
  if (StmtHasForkJoin(stmt->then_branch)) return true;
  if (StmtHasForkJoin(stmt->else_branch)) return true;
  if (StmtHasForkJoin(stmt->body)) return true;
  if (StmtHasForkJoin(stmt->for_body)) return true;
  for (const auto& ci : stmt->case_items)
    if (StmtHasForkJoin(ci.body)) return true;
  return false;
}

static bool MayInferLatch(const Stmt* stmt);

static bool MayInferLatchCase(const Stmt* stmt) {
  bool has_default = false;
  for (const auto& ci : stmt->case_items)
    if (ci.is_default) {
      has_default = true;
      break;
    }
  if (!has_default) return true;
  for (const auto& ci : stmt->case_items)
    if (MayInferLatch(ci.body)) return true;
  return false;
}

static bool MayInferLatch(const Stmt* stmt) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kIf:
      if (!stmt->else_branch) return true;
      return MayInferLatch(stmt->then_branch) ||
             MayInferLatch(stmt->else_branch);
    case StmtKind::kCase:
      return MayInferLatchCase(stmt);
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts)
        if (MayInferLatch(s)) return true;
      return false;
    default:
      return false;
  }
}

// Detects statement-level timing controls (delay, event, wait, wait fork). When
// `include_intra_assign` is set, an assignment carrying an intra-assignment
// timing control (`x = #5 y;`, `x <= @(clk) y;`, `x = ##2 y;`, the repeat-event
// form) also counts — a form legal for some always procedures (e.g. a
// nonblocking delay in always_comb, §9.2.2.2) but not for a final procedure,
// which is limited to the timing-free statements permitted in a function.
static bool StmtHasTimingControl(const Stmt* stmt,
                                 bool include_intra_assign = false) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kTimingControl:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
      return true;
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      return include_intra_assign &&
             (stmt->delay != nullptr || stmt->cycle_delay != nullptr ||
              !stmt->events.empty());
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts)
        if (StmtHasTimingControl(s, include_intra_assign)) return true;
      return false;
    case StmtKind::kIf:
      return StmtHasTimingControl(stmt->then_branch, include_intra_assign) ||
             StmtHasTimingControl(stmt->else_branch, include_intra_assign);
    case StmtKind::kFor:
      return StmtHasTimingControl(stmt->for_body, include_intra_assign);
    case StmtKind::kWhile:
    case StmtKind::kDoWhile:
    case StmtKind::kForever:
    case StmtKind::kRepeat:
    case StmtKind::kForeach:
      return StmtHasTimingControl(stmt->body, include_intra_assign);
    case StmtKind::kFork:
      for (const auto* s : stmt->fork_stmts)
        if (StmtHasTimingControl(s, include_intra_assign)) return true;
      return false;
    case StmtKind::kCase:
      for (const auto& ci : stmt->case_items)
        if (StmtHasTimingControl(ci.body, include_intra_assign)) return true;
      return false;
    default:
      return false;
  }
}

static void ValidateCombLatchProcess(ModuleItem* item, const RtlirProcess& proc,
                                     RtlirProcessKind kind, DiagEngine& diag) {
  if (kind != RtlirProcessKind::kAlwaysComb &&
      kind != RtlirProcessKind::kAlwaysLatch)
    return;
  const char* kw =
      (kind == RtlirProcessKind::kAlwaysComb) ? "always_comb" : "always_latch";
  // §9.2.2.2.2 / §9.2.2.3: an always_comb (and, by reference, always_latch)
  // infers its own sensitivity and shall not carry an explicit event control;
  // the parser stores such a control in the block's sensitivity list.
  if (!item->sensitivity.empty() || item->is_star_sensitivity) {
    diag.Error(item->loc,
               std::format("{} shall not have an explicit event control", kw));
  }
  if (StmtHasTimingControl(proc.body)) {
    diag.Error(item->loc,
               std::format("{} shall not contain timing controls", kw));
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               std::format("{} shall not contain fork-join statements", kw));
  }
  if (kind == RtlirProcessKind::kAlwaysComb && MayInferLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_comb may infer latched behavior; "
                 "ensure all paths assign all outputs");
  }
  if (kind == RtlirProcessKind::kAlwaysLatch && !MayInferLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_latch does not infer latched behavior; "
                 "ensure incomplete assignments create intended latches");
  }
}

static void ValidateAlwaysFFProcess(ModuleItem* item, const RtlirProcess& proc,
                                    DiagEngine& diag) {
  if (item->sensitivity.empty()) {
    diag.Error(item->loc, "always_ff requires an event control");
  }
  if (StmtHasTimingControl(proc.body)) {
    diag.Error(item->loc,
               "always_ff shall not contain blocking timing controls");
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc, "always_ff shall not contain fork-join statements");
  }
  bool has_edge = false;
  for (const auto& ev : item->sensitivity) {
    if (ev.edge == Edge::kPosedge || ev.edge == Edge::kNegedge) {
      has_edge = true;
      break;
    }
  }
  if (!item->sensitivity.empty() && !has_edge) {
    diag.Warning(item->loc,
                 "always_ff has no edge-sensitive event; "
                 "may not represent sequential logic");
  }
}

static void ValidateFinalProcess(ModuleItem* item, const RtlirProcess& proc,
                                 DiagEngine& diag) {
  if (StmtHasTimingControl(proc.body, /*include_intra_assign=*/true)) {
    diag.Error(item->loc, "final procedure shall not contain timing controls");
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               "final procedure shall not contain fork-join statements");
  }
}

static RtlirProcess BuildProcessWithSensitivity(
    RtlirProcessKind kind, ModuleItem* item, Arena& arena,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_map) {
  RtlirProcess proc;
  proc.kind = kind;
  proc.body = item->body;
  proc.sensitivity = item->sensitivity;
  proc.is_star_sensitivity = item->is_star_sensitivity;
  bool needs_infer = (kind == RtlirProcessKind::kAlwaysComb ||
                      kind == RtlirProcessKind::kAlwaysLatch);
  if (needs_infer && proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, arena, func_map);
  }
  if (kind == RtlirProcessKind::kAlways && item->is_star_sensitivity &&
      proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, arena, nullptr, false);
  }
  return proc;
}

static void ValidateProcess(RtlirProcessKind kind, ModuleItem* item,
                            const RtlirProcess& proc, DiagEngine& diag) {
  if (kind == RtlirProcessKind::kAlways && item->sensitivity.empty() &&
      !item->is_star_sensitivity && !StmtHasTimingControl(proc.body)) {
    diag.Warning(item->loc,
                 "always block has no timing control; may cause "
                 "a zero-delay loop");
  }
  ValidateCombLatchProcess(item, proc, kind, diag);
  if (kind == RtlirProcessKind::kAlwaysFF) {
    ValidateAlwaysFFProcess(item, proc, diag);
  }
  if (kind == RtlirProcessKind::kFinal) {
    ValidateFinalProcess(item, proc, diag);
  }
}

void AddProcess(RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod,
                const ProcessBuildEnv& env) {
  RtlirProcess proc =
      BuildProcessWithSensitivity(kind, item, env.arena, env.func_map);
  ValidateProcess(kind, item, proc, env.diag);
  proc.attrs = ResolveAttributes(item->attrs, env.diag);
  mod->processes.push_back(proc);
}

static void CollectStmtLhsPrefixes(const Stmt* stmt,
                                   std::unordered_set<std::string>& out,
                                   const ScopeMap& scope) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    if (stmt->lhs) {
      // §11.5.3: an indexing select stays inside the longest static prefix only
      // when its index is a constant expression. The module parameter scope is
      // threaded in so that a localparam/parameter index (a constant form of
      // §11.2.1) resolves to a value and keeps the select in the prefix, rather
      // than being mistaken for a run-time index and collapsing the prefix to
      // the base identifier -- which would flag distinct constant-indexed
      // elements as one over-driven target.
      std::string prefix = LongestStaticPrefix(stmt->lhs, scope);
      if (!prefix.empty()) out.insert(std::move(prefix));
    }
  }
  for (const auto* s : stmt->stmts) CollectStmtLhsPrefixes(s, out, scope);
  CollectStmtLhsPrefixes(stmt->then_branch, out, scope);
  CollectStmtLhsPrefixes(stmt->else_branch, out, scope);
  CollectStmtLhsPrefixes(stmt->body, out, scope);
  CollectStmtLhsPrefixes(stmt->for_body, out, scope);
  for (auto* fi : stmt->for_inits) CollectStmtLhsPrefixes(fi, out, scope);
  for (auto* fs : stmt->for_steps) CollectStmtLhsPrefixes(fs, out, scope);
  for (const auto& ci : stmt->case_items)
    CollectStmtLhsPrefixes(ci.body, out, scope);
  for (const auto* s : stmt->fork_stmts) CollectStmtLhsPrefixes(s, out, scope);
}

static void CollectCallNamesExpr(const Expr* expr,
                                 std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    out.insert(expr->callee);
  CollectCallNamesExpr(expr->lhs, out);
  CollectCallNamesExpr(expr->rhs, out);
  CollectCallNamesExpr(expr->condition, out);
  CollectCallNamesExpr(expr->true_expr, out);
  CollectCallNamesExpr(expr->false_expr, out);
  CollectCallNamesExpr(expr->base, out);
  CollectCallNamesExpr(expr->index, out);
  for (auto* arg : expr->args) CollectCallNamesExpr(arg, out);
  for (auto* elem : expr->elements) CollectCallNamesExpr(elem, out);
}

static void CollectCallNamesStmt(const Stmt* stmt,
                                 std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  CollectCallNamesExpr(stmt->expr, out);
  CollectCallNamesExpr(stmt->rhs, out);
  CollectCallNamesExpr(stmt->condition, out);
  CollectCallNamesExpr(stmt->for_cond, out);
  for (const auto* s : stmt->stmts) CollectCallNamesStmt(s, out);
  CollectCallNamesStmt(stmt->then_branch, out);
  CollectCallNamesStmt(stmt->else_branch, out);
  CollectCallNamesStmt(stmt->body, out);
  CollectCallNamesStmt(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectCallNamesStmt(fi, out);
  for (auto* fs : stmt->for_steps) CollectCallNamesStmt(fs, out);
  for (const auto& ci : stmt->case_items) CollectCallNamesStmt(ci.body, out);
  for (const auto* s : stmt->fork_stmts) CollectCallNamesStmt(s, out);
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
      for (auto* s : it->second->func_body_stmts) {
        CollectStmtLhsPrefixes(s, out, scope);
        CollectCallNamesStmt(s, next);
      }
    }
    pending = std::move(next);
  }
}

static bool PrefixesOverlap(const std::string& a, const std::string& b) {
  if (a == b) return true;
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

static void CollectProcessLhsInfo(
    const ModuleDecl* decl, std::vector<ProcInfo>& procs,
    std::unordered_set<std::string>& cont_assign_lhs,
    std::unordered_set<std::string>& general_proc_lhs, const FuncMap* func_map,
    const ScopeMap& scope) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock) {
      ProcInfo info;
      info.loc = item->loc;
      info.kind = item->kind;
      CollectStmtLhsPrefixes(item->body, info.lhs, scope);
      if (func_map && !func_map->empty())
        CollectFuncLhsPrefixes(item->body, *func_map, info.lhs, scope);
      procs.push_back(std::move(info));
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs, scope);
      if (!prefix.empty()) cont_assign_lhs.insert(std::move(prefix));
    }
    // §9.2.2.2: an always_comb LHS shall not be assigned by any other process,
    // which includes a general-purpose always block or an initial block. Their
    // assignment targets are gathered separately so an overlap with an
    // always_comb prefix can be flagged.
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kInitialBlock) {
      CollectStmtLhsPrefixes(item->body, general_proc_lhs, scope);
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
                               prefix));
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
      diag.Error(proc.loc, std::format("variable '{}' driven by {} and "
                                       "continuous assignment",
                                       var, ProcessKindLabel(proc.kind)));
      break;
    }
  }
}

// §9.2.2.2: report an always_comb LHS that is also assigned by a general
// process (a plain always block or an initial block). This is restricted to
// always_comb targets so the diagnostic stays within this subclause's rule;
// the analogous single-driver rules for always_latch and always_ff belong to
// §9.2.2.3 / §9.2.2.4. Element granularity comes for free from the longest
// static prefix (§11.5.3): distinct array elements or struct fields do not
// overlap and so are not reported.
static void CheckGeneralProcConflict(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (const auto& proc : procs) {
    if (proc.kind != ModuleItemKind::kAlwaysCombBlock) continue;
    for (const auto& var : proc.lhs) {
      for (const auto& other : general_proc_lhs) {
        if (PrefixesOverlap(var, other)) {
          diag.Error(proc.loc,
                     std::format("variable '{}' driven by always_comb and "
                                 "another process",
                                 var));
          break;
        }
      }
    }
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
  // The module parameter scope lets §11.5.3's longest-static-prefix analysis
  // treat a localparam/parameter index as the constant expression it is.
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  CollectProcessLhsInfo(decl, procs, cont_assign_lhs, general_proc_lhs,
                        &func_decls_, scope);
  CheckDriverConflicts(procs, cont_assign_lhs, general_proc_lhs, diag_);
}

// §6.5: the single-driver rule is stated per term of a variable's longest
// static prefix, so distinct elements of an aggregate (a struct member or an
// array/part-select element) are independent driver targets. The name-keyed
// cross-checks (ValidateContAssignIdentLhs / ValidateMixedAssignments) collapse
// every element to the base variable name and so can only police whole-variable
// targets; CheckAlwaysCombMultiDriver covers element granularity but only for
// always_comb/always_latch/always_ff processes. This pass closes the remaining
// gap for a continuous assignment whose target is an aggregate element: it
// flags a second continuous driver, or a general procedural (initial / always)
// driver, whose longest static prefix overlaps. Prefixes that are bare
// identifiers stay with the name-keyed checks, and always_comb/latch/ff
// processes stay with CheckAlwaysCombMultiDriver, so no conflict is reported
// twice.
void Elaborator::CheckAggregateElementDrivers(const ModuleDecl* decl,
                                              RtlirModule* mod) {
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};

  struct ContTarget {
    std::string prefix;
    bool aggregate;
    SourceLoc loc;
  };
  std::vector<ContTarget> conts;
  std::unordered_set<std::string> proc_prefixes;

  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs, scope);
      if (prefix.empty()) continue;
      bool aggregate = prefix.find('.') != std::string::npos ||
                       prefix.find('[') != std::string::npos;
      conts.push_back({std::move(prefix), aggregate, item->loc});
    }
    // Only general initial/always blocks are gathered here; always_comb,
    // always_latch, and always_ff are already handled by
    // CheckAlwaysCombMultiDriver.
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock) {
      CollectStmtLhsPrefixes(item->body, proc_prefixes, scope);
    }
  }

  // Multiple continuous assignments writing to overlapping element prefixes.
  // Whole-identifier vs whole-identifier pairs are already diagnosed by
  // ValidateContAssignIdentLhs, so at least one side of a reported pair must be
  // an aggregate element.
  for (size_t i = 0; i < conts.size(); ++i) {
    for (size_t j = i + 1; j < conts.size(); ++j) {
      if (!conts[i].aggregate && !conts[j].aggregate) continue;
      if (PrefixesOverlap(conts[i].prefix, conts[j].prefix)) {
        diag_.Error(conts[j].loc,
                    std::format("multiple continuous assignments drive "
                                "overlapping element '{}'",
                                conts[j].prefix));
      }
    }
  }

  // A continuous assignment to an aggregate element mixed with a procedural
  // driver of an overlapping prefix. The whole-identifier form is handled by
  // ValidateMixedAssignments, so only aggregate continuous targets are checked.
  for (const auto& ct : conts) {
    if (!ct.aggregate) continue;
    for (const auto& pp : proc_prefixes) {
      if (PrefixesOverlap(ct.prefix, pp)) {
        diag_.Error(ct.loc,
                    std::format("element '{}' has both a continuous assignment "
                                "and a procedural assignment",
                                ct.prefix));
        break;
      }
    }
  }
}

}  // namespace delta
