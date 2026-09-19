#include <cstddef>
#include <cstdint>
#include <format>
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
  std::string_view name = LhsSignalName(lhs);
  if (name.empty()) return 0;
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

// §14.14: an event control naming $global_clock in the procedure body waits on
// the event expression of the global clocking declaration in scope, so it is
// rewritten into that expression here, where the body reaches the process.
//
// The rewrite is made on a copy of the statement rather than in place because
// `item` belongs to the one ModuleDecl the parser built for the module, while
// Elaborator::ElaborateModule runs once per instantiation of it: every
// instance of a module builds its processes from the same Stmt objects, so a
// statement written in place would carry one instance's substitution into
// every other instance. Keep any further per-instance rewrite of a process
// body on a copy for the same reason.
//
// SubstituteGlobalClockEventControls returns `item->body` itself where nothing
// was rewritten, which is every procedure that does not name $global_clock, so
// the copy costs an allocation only where the rewrite is actually made.
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
  // §14.14: a procedure whose sensitivity list is the single clocking event
  // $global_clock waits on the effective global clocking declaration's event
  // expression. The substitution is made on the process's own copy because
  // `item` belongs to the one ModuleDecl the parser built for the module while
  // this runs once per instantiation, and rule b) can give two instances
  // different events; writing `item` would give both whichever came first.
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
                const ProcessBuildEnv& env) {
  RtlirProcess proc = BuildProcessWithSensitivity(kind, item, env);
  ValidateProcess(kind, item, proc, env.diag);
  proc.attrs = ResolveAttributes(item->attrs, env.diag);
  mod->processes.push_back(proc);
}

// Collects the longest static prefix (§11.5.3) of every assignment target
// written in `stmt` or in any statement nested inside it.
//
// §9.2.2.2 states its rule of "the variables assigned on the left-hand side of
// assignments" and §10.3.2 of "any procedural assignment"; neither puts a
// condition on which statement the assignment stands in, so every position a
// statement holds a statement in is a position this collection reaches.
//
// This is a collector, so a position it does not reach costs a name rather than
// a report. The callers below compare the names gathered here against each
// other and against the continuous-assignment targets, and a name that was
// never gathered overlaps nothing: a variable assigned only in the unreached
// position stays absent from every set, so §9.2.2.2's "shall not be assigned by
// any other process" and §10.3.2's "It shall be an error for a variable driven
// by a continuous assignment or output to have ... any procedural assignment"
// both pass it in silence, however many drivers it has. The unreached position
// is an exemption from the single-driver rule rather than a missing diagnostic.
//
// ForEachChildStmt in elaborator_validate_internal.h states those positions
// once for the whole elaborator, which is why the list is not written out again
// here. The visitor takes `Stmt* const&` because `stmt` is a `const Stmt*`,
// which is how ForEachChildStmt lets a walk that only reads the tree share its
// list with the walks that rewrite it.
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
  ForEachChildStmt(
      stmt, [&](Stmt* const& sub) { CollectStmtLhsPrefixes(sub, out, scope); });
}

// Collects the name of every subroutine called from `expr` or from any
// expression nested inside it. AnyExprChild in elaborator_validate_internal.h
// states the links an Expr holds, which is why the list is not written out
// again here. This walk named nine of the thirteen, and the four it left out
// are positions a call is written in: `w[3:f()]` puts one in Expr::index_end,
// `q.sum() with (f())` in Expr::with_expr, `{f(){1'b0}}` in Expr::repeat_count,
// and `'{f(): 1}` in Expr::pattern_keys.
static void CollectCallNamesExpr(const Expr* expr,
                                 std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    out.insert(expr->callee);
  ForEachExprChild(
      expr, [&](const Expr* child) { CollectCallNamesExpr(child, out); });
}

// Collects the name of every subroutine called from `stmt` or from any
// statement nested inside it. §9.2.2.2 says of an always_comb procedure that
// "The variables assigned on the left-hand side of assignments shall not be
// assigned by any other process. This includes variables assigned within
// functions called by the procedure but not those assigned within tasks called
// by the procedure." It states no condition on where in the procedure the call
// is written, so every position a statement holds an expression in is a
// position a call reaches the rule from.
//
// This is a collector, so a position it does not reach costs a name rather than
// a report. CollectFuncLhsPrefixes below takes the names gathered here, and no
// others, as the roots of its search of the function bodies; a function called
// only from an unreached position is therefore never opened, its assignment
// targets never join the procedure's own, and the variables it assigns are
// exempt from that sentence however many other processes assign them. The same
// holds one level down, since the closure re-enters this walk over each
// function body it does open.
//
// ForEachChildExpr states the positions a statement holds an expression in and
// ForEachChildStmt the positions it holds a statement in, both in
// elaborator_validate_internal.h, which is why neither list is written out
// again here. This walk named four of the sixteen expression positions, and the
// twelve it left out are positions a call is written in: `int k = f();` puts
// one in Stmt::var_init, `w[f()] = 1;` under Stmt::lhs, `z <= #(f()) a;` in
// Stmt::delay, `assert (f());` in Stmt::assert_expr, and a case-item pattern
// and a randcase weight each hold one too.
static void CollectCallNamesStmt(const Stmt* stmt,
                                 std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  ForEachChildExpr(stmt, [&](Expr* const& e) { CollectCallNamesExpr(e, out); });
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CollectCallNamesStmt(sub, out); });
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

// §9.2.2.2/§6.5: the driver targets a module's items contribute, each as a
// longest static prefix (§11.5.3) -- one entry per always_comb/always_latch/
// always_ff process, the targets of every continuous assignment, and the
// targets of every general procedural (always/initial) block.
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

// §11.5.3: the assignment targets of one always_comb/always_latch/always_ff
// process, as longest static prefixes. A target reached through a function call
// counts as the process's own.
static ProcInfo MakeProcInfo(const ModuleItem* item, const FuncMap* func_map,
                             const ScopeMap& scope) {
  ProcInfo info;
  info.loc = item->loc;
  info.kind = item->kind;
  CollectStmtLhsPrefixes(item->body, info.lhs, scope);
  if (func_map && !func_map->empty())
    CollectFuncLhsPrefixes(item->body, *func_map, info.lhs, scope);
  return info;
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
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs, scope);
      if (!prefix.empty()) drivers.cont_assign_lhs.insert(std::move(prefix));
    }
    // §9.2.2.2: the variables an always_comb assigns "shall not be assigned by
    // any other process". §9.2 makes the general purpose always procedure, the
    // initial procedure and the final procedure each a process, so all three
    // are gathered here; their assignment targets are kept apart from `procs`
    // so an overlap with an always_comb prefix can be flagged. always_comb,
    // always_latch and always_ff are the ones that go into `procs` instead,
    // because a process is also compared against the other two of its own three
    // kinds rather than only against an always_comb.
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      CollectStmtLhsPrefixes(item->body, drivers.general_proc_lhs, scope);
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

// §9.2.2.2: report an always_comb LHS that is also assigned by a general
// process (a plain always block or an initial block). §9.2.2.3 states that all
// of §9.2.2.2's rules apply to always_latch, so a latch target sharing a prefix
// with a general procedural driver is flagged the same way. always_ff's
// analogous single-driver rule is left to §9.2.2.4. Element granularity comes
// for free from the longest static prefix (§11.5.3): distinct array elements or
// struct fields do not overlap and so are not reported.
static void CheckGeneralProcOverlap(
    const std::string& var, const ProcInfo& proc,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (const auto& other : general_proc_lhs) {
    if (PrefixesOverlap(var, other)) {
      diag.Error(proc.loc,
                 std::format("variable '{}' driven by {} and "
                             "another process",
                             var, ProcessKindLabel(proc.kind)),
                 Subclause("9.2.2.2"));
      return;
    }
  }
}

static void CheckGeneralProcConflict(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (const auto& proc : procs) {
    if (proc.kind != ModuleItemKind::kAlwaysCombBlock &&
        proc.kind != ModuleItemKind::kAlwaysLatchBlock)
      continue;
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
  // The module parameter scope lets §11.5.3's longest-static-prefix analysis
  // treat a localparam/parameter index as the constant expression it is.
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  CollectProcessLhsInfo(decl, {procs, cont_assign_lhs, general_proc_lhs},
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
// §6.5: one continuous-assignment target, as a longest static prefix, with a
// note of whether that prefix reaches into an aggregate (a struct member or an
// array/part-select element) rather than naming a whole variable.
struct ContTarget {
  std::string prefix;
  bool aggregate;
  SourceLoc loc;
};

// Gather the continuous-assignment targets of `decl` and the assignment targets
// of its general procedural blocks. always_comb, always_latch, and always_ff
// are left out: CheckAlwaysCombMultiDriver already covers them at element
// granularity. The initial, always and final procedures §9.2 defines have no
// such second pass, so all three are gathered here.
static void CollectAggregateDriverTargets(
    const ModuleDecl* decl, const ScopeMap& scope,
    std::vector<ContTarget>& conts,
    std::unordered_set<std::string>& proc_prefixes) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs, scope);
      if (prefix.empty()) continue;
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

// Multiple continuous assignments writing to overlapping element prefixes.
// Whole-identifier vs whole-identifier pairs are already diagnosed by
// ValidateContAssignIdentLhs, so at least one side of a reported pair must be
// an aggregate element.
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
                   Subclause("10.3.2"));
      }
    }
  }
}

// A continuous assignment to an aggregate element mixed with a procedural
// driver of an overlapping prefix. The whole-identifier form is handled by
// ValidateMixedAssignments, so only aggregate continuous targets are checked.
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
  std::vector<ContTarget> conts;
  std::unordered_set<std::string> proc_prefixes;
  CollectAggregateDriverTargets(decl, scope, conts, proc_prefixes);
  CheckOverlappingContTargets(conts, diag_);
  CheckContProcElementMix(conts, proc_prefixes, diag_);
}

}  // namespace delta
