#include "simulator/specify.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"

namespace delta {

uint64_t ClampPathDelay(int64_t signed_value) {
  return signed_value < 0 ? 0u : static_cast<uint64_t>(signed_value);
}

void ExpandTransitionDelays(PathDelay& pd) {
  switch (pd.delay_count) {
    case 1: {
      const uint64_t kT = pd.delays[0];
      for (int i = 1; i < 6; ++i) pd.delays[i] = kT;
      break;
    }
    case 2: {
      const uint64_t kTrise = pd.delays[0];
      const uint64_t kTfall = pd.delays[1];
      pd.delays[2] = kTrise;
      pd.delays[3] = kTrise;
      pd.delays[4] = kTfall;
      pd.delays[5] = kTfall;
      break;
    }
    case 3: {
      const uint64_t kTrise = pd.delays[0];
      const uint64_t kTfall = pd.delays[1];
      const uint64_t kTz = pd.delays[2];
      pd.delays[3] = kTrise;
      pd.delays[4] = kTz;
      pd.delays[5] = kTfall;
      break;
    }
    default:

      break;
  }

  if (pd.delay_count == 12) return;
  pd.delays[6] = std::min(pd.delays[2], pd.delays[0]);
  pd.delays[7] = std::max(pd.delays[3], pd.delays[0]);
  pd.delays[8] = std::min(pd.delays[4], pd.delays[1]);
  pd.delays[9] = std::max(pd.delays[5], pd.delays[1]);
  pd.delays[10] = std::max(pd.delays[4], pd.delays[2]);
  pd.delays[11] = std::min(pd.delays[3], pd.delays[5]);
}

// Record a specparam name once; a name already collected is not repeated.
static void AddSpecparamName(std::vector<std::string>& names,
                             std::string_view name) {
  if (name.empty()) return;
  for (const auto& seen : names) {
    if (seen == name) return;
  }
  names.emplace_back(name);
}

std::vector<std::string> CollectDeclaredSpecparams(const ModuleDecl& mod) {
  std::vector<std::string> names;
  for (const auto* item : mod.items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kSpecparam) {
      AddSpecparamName(names, item->name);
      continue;
    }
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (const auto* si : item->specify_items) {
      if (si != nullptr && si->kind == SpecifyItemKind::kSpecparam)
        AddSpecparamName(names, si->param_name);
    }
  }
  return names;
}

bool ExprReadsSpecparam(const Expr* expr,
                        const std::vector<std::string>& specparams);

// True when any element of a concatenation, assignment pattern, or replication
// reads one of the specparams.
static bool AnyElementReadsSpecparam(
    const std::vector<Expr*>& elements,
    const std::vector<std::string>& specparams) {
  for (const auto* el : elements) {
    if (ExprReadsSpecparam(el, specparams)) return true;
  }
  return false;
}

bool ExprReadsSpecparam(const Expr* expr,
                        const std::vector<std::string>& specparams) {
  if (expr == nullptr) return false;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& name : specparams) {
        if (name == expr->text) return true;
      }
      return false;
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      return ExprReadsSpecparam(expr->lhs, specparams);
    case ExprKind::kBinary:
      return ExprReadsSpecparam(expr->lhs, specparams) ||
             ExprReadsSpecparam(expr->rhs, specparams);
    case ExprKind::kTernary:
      return ExprReadsSpecparam(expr->condition, specparams) ||
             ExprReadsSpecparam(expr->true_expr, specparams) ||
             ExprReadsSpecparam(expr->false_expr, specparams);
    case ExprKind::kMinTypMax:
      return ExprReadsSpecparam(expr->lhs, specparams) ||
             ExprReadsSpecparam(expr->condition, specparams) ||
             ExprReadsSpecparam(expr->rhs, specparams);
    case ExprKind::kSelect:
      return ExprReadsSpecparam(expr->base, specparams) ||
             ExprReadsSpecparam(expr->index, specparams) ||
             ExprReadsSpecparam(expr->index_end, specparams);
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
      return AnyElementReadsSpecparam(expr->elements, specparams);
    case ExprKind::kReplicate:
      return ExprReadsSpecparam(expr->repeat_count, specparams) ||
             AnyElementReadsSpecparam(expr->elements, specparams);
    default:
      return false;
  }
}

namespace {

// §32.4.1: how many leading terminals of a gate instantiation are outputs.
// The buffer/inverter family drives every terminal but the trailing input; the
// logic-gate, three-state-buffer and MOS-switch families drive their first
// terminal; a pullup/pulldown drives all of them; the bidirectional pass-gate
// family drives none, so a DEVICE delay has no primitive of its own to land on.
std::size_t GateOutputTerminalCount(GateKind kind, std::size_t terminals) {
  switch (kind) {
    case GateKind::kBuf:
    case GateKind::kNot:
      return terminals == 0 ? 0 : terminals - 1;
    case GateKind::kPullup:
    case GateKind::kPulldown:
      return terminals;
    case GateKind::kTran:
    case GateKind::kRtran:
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:
      return 0;
    default:
      return terminals == 0 ? 0 : 1;
  }
}

// §32.4.1: evaluate the gate's declared delay expressions into the twelve
// transition slots. A gate lists at most a rise, a fall, and a turnoff delay,
// which spread over the slots exactly as a module path's one/two/three delay
// list does.
void FillPrimitiveDriverDelays(PrimitiveDriver& driver, const ModuleItem& gate,
                               SimContext& ctx, Arena& arena) {
  Expr* const kDelayExprs[3] = {gate.gate_delay, gate.gate_delay_fall,
                                gate.gate_delay_decay};
  PathDelay scratch;
  std::size_t count = 0;
  for (Expr* delay_expr : kDelayExprs) {
    if (delay_expr == nullptr) break;
    Logic4Vec value = EvalExpr(delay_expr, ctx, arena);
    const uint32_t kWidth = value.width == 0 ? 64u : value.width;
    const int64_t kSigned = SignExtend(value.ToUint64(), kWidth);
    scratch.delays[count] = ClampPathDelay(kSigned);
    ++count;
  }
  scratch.delay_count = static_cast<uint8_t>(count == 0 ? 1 : count);
  ExpandTransitionDelays(scratch);
  driver.delay_count = scratch.delay_count;
  for (int i = 0; i < 12; ++i) driver.delays[i] = scratch.delays[i];
}

}  // namespace

std::vector<PrimitiveDriver> BuildPrimitiveDriversFromGate(
    const ModuleItem& gate, SimContext& ctx, Arena& arena) {
  std::vector<PrimitiveDriver> drivers;
  const std::size_t kOutputs =
      GateOutputTerminalCount(gate.gate_kind, gate.gate_terminals.size());
  for (std::size_t i = 0; i < kOutputs; ++i) {
    const Expr* terminal = gate.gate_terminals[i];
    // Only a terminal that names a signal outright identifies an output this
    // annotator can match a DEVICE operand against.
    if (terminal == nullptr || terminal->kind != ExprKind::kIdentifier) {
      continue;
    }
    PrimitiveDriver driver;
    driver.output_port = std::string(terminal->text);
    FillPrimitiveDriverDelays(driver, gate, ctx, arena);
    drivers.push_back(std::move(driver));
  }
  return drivers;
}

// The greatest transition time among the candidates §30.5.3 admits: those that
// name a path and whose condition holds.
//
// The condition is tested here and again in SelectActivePath below, and taking
// it first is the point. §30.5.3 states both halves in one sentence -- active
// paths are "those whose input has transitioned most recently in time, and
// either they have no condition or their conditions are true" -- and reading
// the time first lets a path whose condition is false set it and drop every
// live path at an earlier one, leaving nothing to govern an output that is
// plainly transitioning.
static uint64_t GreatestAdmittedTransitionTime(
    const std::vector<PathCandidate>& candidates) {
  uint64_t max_time = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr || !c.condition_true) continue;
    if (c.last_transition_time > max_time) max_time = c.last_transition_time;
  }
  return max_time;
}

const PathDelay* SelectActivePath(const std::vector<PathCandidate>& candidates,
                                  uint8_t transition_slot) {
  if (candidates.empty()) return nullptr;

  uint64_t max_time = GreatestAdmittedTransitionTime(candidates);
  const PathDelay* best_path = nullptr;
  uint64_t best = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr) continue;
    if (!c.condition_true) continue;
    if (c.last_transition_time != max_time) continue;
    uint64_t d = c.path->delays[transition_slot];
    if (best_path == nullptr || d < best) {
      best = d;
      best_path = c.path;
    }
  }
  return best_path;
}

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot) {
  const PathDelay* selected = SelectActivePath(candidates, transition_slot);
  return selected ? selected->delays[transition_slot] : 0;
}

bool StateDependentPathConditionEnables(Logic4Word condition_lsb) {
  // An unknown (x or z) condition counts as true; otherwise the path is active
  // only when the least-significant bit of the result is 1.
  const bool kUnknown = (condition_lsb.bval & 1u) != 0u;
  if (kUnknown) return true;
  return (condition_lsb.aval & 1u) != 0u;
}

void ReplacePathDelayPreservingPulse(PathDelay& existing, PathDelay replacement,
                                     PathDelayPulseRetention retain) {
  uint64_t saved_reject[12];
  uint64_t saved_error[12];
  for (int i = 0; i < 12; ++i) {
    saved_reject[i] = existing.reject_limit[i];
    saved_error[i] = existing.error_limit[i];
  }
  PulseLimitSource saved_reject_source = existing.reject_limit_source;
  PulseLimitSource saved_error_source = existing.error_limit_source;
  existing = std::move(replacement);
  // §30.7.3: a limit kept from the path being replaced keeps the standing of
  // the source that set it, so a later source of lower precedence does not
  // reach a limit it could not have reached before the replacement.
  if (retain.reject) {
    for (int i = 0; i < 12; ++i) existing.reject_limit[i] = saved_reject[i];
    existing.reject_limit_source = saved_reject_source;
  }
  if (retain.error) {
    for (int i = 0; i < 12; ++i) existing.error_limit[i] = saved_error[i];
    existing.error_limit_source = saved_error_source;
  }
}

namespace {

// Nonconditional update: overwrites every existing path delay between the same
// ports, but keeps each entry's original condition/ifnone (and whichever pulse
// limits are being held). Returns true if at least one entry matched.
//
// §30.3 puts a specify block inside a module declaration, so two instances of
// one cell declare paths carrying the same src_port and dst_port and are told
// apart only by PathDelay::inst_prefix. `match_inst_prefix` asks for that
// comparison: SpecifyManager::AddPathDelay sets it, so registering a second
// instance adds a path rather than overwriting the first instance's.
bool UpdateNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                    const PathDelay& delay,
                                    PathDelayPulseRetention retain,
                                    bool match_inst_prefix) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.src_select == delay.src_select &&
        existing.dst_select == delay.dst_select &&
        (!match_inst_prefix || existing.inst_prefix == delay.inst_prefix)) {
      std::string saved_cond = existing.condition;
      bool saved_ifnone = existing.is_ifnone;
      ReplacePathDelayPreservingPulse(existing, delay, retain);
      existing.condition = std::move(saved_cond);
      existing.is_ifnone = saved_ifnone;
      matched = true;
    }
  }
  return matched;
}

// §32.4.1 (printed page 925): whether the SDF entry `entry` names the declared
// path `existing` by what it wrote on the ports beyond their names -- ports
// and instance being compared by each caller. An entry whose source was
// written with an edge, `(IOPATH (posedge clk) q ...)`, names the path
// declared with that edge, and one whose port was written with a select,
// `(IOPATH a[1] y ...)`, the path declared with that select; one written with
// neither names the path whatever edge or select it was declared with.
bool SdfEntryNamesPath(const PathDelay& existing, const PathDelay& entry) {
  return (entry.edge == SpecifyEdge::kNone || existing.edge == entry.edge) &&
         (entry.src_select.empty() ||
          existing.src_select == entry.src_select) &&
         (entry.dst_select.empty() || existing.dst_select == entry.dst_select);
}

// §32.3: an entry that names no declared path is still kept, under the ports as
// the SDF file wrote them, so that one written with a select -- whose ports
// hold the bare names while it is matched -- is not taken at run time for a
// path from the whole port.
PathDelay SdfEntryAsWritten(PathDelay entry) {
  entry.src_port += entry.src_select;
  entry.dst_port += entry.dst_select;
  entry.src_select.clear();
  entry.dst_select.clear();
  return entry;
}

// §32.4.1: an SDF entry carries delays and pulse limits and nothing of the
// path's shape, so the path it lands on keeps what its declaration gave it --
// its kind, its edge, its selects and its condition, as text and as the
// expression §30.5.3 selects on. Replaced whole, an edge-sensitive path took
// the entry's edge, none, and a conditional one lost the expression.
void ReplaceWithSdfDelays(PathDelay& existing, PathDelay entry,
                          PathDelayPulseRetention retain) {
  entry.path_kind = existing.path_kind;
  entry.edge = existing.edge;
  entry.src_select = existing.src_select;
  entry.dst_select = existing.dst_select;
  entry.condition = existing.condition;
  entry.condition_expr = existing.condition_expr;
  entry.is_ifnone = existing.is_ifnone;
  ReplacePathDelayPreservingPulse(existing, std::move(entry), retain);
}

// §32.4.1 with §32.9: a nonconditional entry lands on every path of the
// instance its cell named (PathDelay::inst_prefix, which SdfCellPrefixInRegion
// in simulator/sdf_annotate.cpp stamped on it) between those two ports that it
// names by edge. Returns true if at least one path matched.
bool AnnotateNonconditionalSdfPaths(std::vector<PathDelay>& path_delays,
                                    const PathDelay& entry,
                                    PathDelayPulseRetention retain) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == entry.src_port &&
        existing.dst_port == entry.dst_port &&
        existing.inst_prefix == entry.inst_prefix &&
        SdfEntryNamesPath(existing, entry)) {
      ReplaceWithSdfDelays(existing, entry, retain);
      matched = true;
    }
  }
  return matched;
}

}  // namespace

void SpecifyManager::AddPathDelay(PathDelay delay, bool preserve_pulse_limits) {
  const PathDelayPulseRetention kRetain{preserve_pulse_limits,
                                        preserve_pulse_limits};
  // A declared path is unconditional when it carries no condition expression,
  // not when its condition renders to no text. SpecifyConditionText in
  // simulator/specify_condition_text.cpp spells a condition for §32.4.1's SDF
  // COND matching and says outright that one it cannot spell yields nothing, so
  // `if (act[i])` and `if (act[j])` both render empty when `i` and `j` are not
  // literals; reading that as unconditional would send every such path through
  // the overwrite-all branch below and leave one. A path built from an SDF
  // record carries no expression and is judged by its text, which is the only
  // thing such a record has.
  const bool kIsNonconditional = delay.condition_expr == nullptr &&
                                 delay.condition.empty() && !delay.is_ifnone;
  if (kIsNonconditional) {
    if (!UpdateNonconditionalPathDelays(path_delays_, delay, kRetain,
                                        /*match_inst_prefix=*/true)) {
      path_delays_.push_back(std::move(delay));
    }
    return;
  }
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.src_select == delay.src_select &&
        existing.dst_select == delay.dst_select &&
        existing.inst_prefix == delay.inst_prefix &&
        SpecifyConditionsMatch(existing.condition, delay.condition) &&
        existing.condition_expr == delay.condition_expr &&
        existing.is_ifnone == delay.is_ifnone) {
      ReplacePathDelayPreservingPulse(existing, std::move(delay), kRetain);
      return;
    }
  }
  path_delays_.push_back(std::move(delay));
}

bool SpecifyManager::AnnotateSdfPathDelay(PathDelay delay,
                                          PathDelayPulseRetention retain) {
  const bool kSdfIsNonconditional = delay.condition.empty() && !delay.is_ifnone;
  if (kSdfIsNonconditional) {
    // §32.4.1: a nonconditional entry reaches all paths between those two
    // ports. Its rule names no restriction to paths already declared, so an
    // entry matching none is still kept, which is how §32.3 chose to hold on to
    // delay data that finds no home.
    if (!AnnotateNonconditionalSdfPaths(path_delays_, delay, retain))
      path_delays_.push_back(SdfEntryAsWritten(std::move(delay)));
    return true;
  }
  // §32.4.1: a conditional entry may land *only* on a path between those same
  // two ports carrying the same condition. Where the module declares no such
  // path there is nothing for it to annotate, so it lands nowhere. Appending
  // one instead would conjure up a specify path the design never wrote, and
  // backannotation only ever updates what a design already declares.
  // The path is one of the instance the entry's cell names (§32.9), so
  // PathDelay::inst_prefix is compared alongside the ports and the condition.
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.inst_prefix == delay.inst_prefix &&
        SpecifyConditionsMatch(existing.condition, delay.condition) &&
        existing.is_ifnone == delay.is_ifnone &&
        SdfEntryNamesPath(existing, delay)) {
      ReplaceWithSdfDelays(existing, std::move(delay), retain);
      return true;
    }
  }
  return false;
}

namespace {

// §32.7: an INCREMENT adds each amount, a negative one lowering the delay, and
// §30.5.1 puts a delay that comes out below zero at zero.
void AddPathDelayValues(PathDelay& existing,
                        const SdfPathDelayIncrement& deltas) {
  for (int i = 0; i < 12; ++i) {
    existing.delays[i] =
        ClampPathDelay(static_cast<int64_t>(existing.delays[i]) + deltas[i]);
  }
}

// Adds `delta` to every existing path delay between the same ports of the same
// instance (ignoring condition/ifnone). Returns true if at least one entry
// matched. PathDelay::inst_prefix is always compared, unlike in
// UpdateNonconditionalPathDelays above: §30.3 puts a specify block inside a
// module declaration, so two instances of one cell hold paths spelled alike,
// and SpecifyManager::IncrementSdfPathDelay is the sole caller and knows which
// instance the SDF entry named.
bool IncrementNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                       const PathDelay& delta,
                                       const SdfPathDelayIncrement& deltas) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port &&
        existing.inst_prefix == delta.inst_prefix &&
        SdfEntryNamesPath(existing, delta)) {
      AddPathDelayValues(existing, deltas);
      matched = true;
    }
  }
  return matched;
}

// Adds `delta` to the first existing path delay matching ports, instance prefix
// and condition/ifnone. Returns true if a matching entry was found.
bool IncrementConditionalPathDelay(std::vector<PathDelay>& path_delays,
                                   const PathDelay& delta,
                                   const SdfPathDelayIncrement& deltas) {
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port &&
        existing.inst_prefix == delta.inst_prefix &&
        SpecifyConditionsMatch(existing.condition, delta.condition) &&
        existing.is_ifnone == delta.is_ifnone &&
        SdfEntryNamesPath(existing, delta)) {
      AddPathDelayValues(existing, deltas);
      return true;
    }
  }
  return false;
}

}  // namespace

bool SpecifyManager::IncrementSdfPathDelay(
    const PathDelay& delta, const SdfPathDelayIncrement& deltas) {
  const bool kSdfIsNonconditional = delta.condition.empty() && !delta.is_ifnone;
  if (kSdfIsNonconditional) {
    // §32.9: the entry reaches the paths of the instance its cell named, which
    // AnnotateSdfIopathEntry (simulator/sdf_annotate_entry.cpp) stamped onto
    // PathDelay::inst_prefix, so it is matched as AnnotateSdfPathDelay does.
    if (!IncrementNonconditionalPathDelays(path_delays_, delta, deltas)) {
      path_delays_.push_back(SdfEntryAsWritten(delta));
    }
    return true;
  }
  // §32.4.1, as above: with no declared path carrying that condition there is
  // nothing to add to.
  return IncrementConditionalPathDelay(path_delays_, delta, deltas);
}

namespace {

void AddInterconnectDelayValues(InterconnectDelay& existing,
                                const InterconnectDelay& delta) {
  existing.rise += delta.rise;
  existing.fall += delta.fall;
  for (int i = 0; i < 12; ++i) existing.delays[i] += delta.delays[i];
}

// §32.5: the entry standing for every source on a load -- what a PORT entry
// leaves behind -- or null where the load carries none.
const InterconnectDelay* FindAllSourceInterconnectDelay(
    const std::vector<InterconnectDelay>& delays, const std::string& load) {
  for (const auto& delay : delays) {
    if (delay.dst_port == load && delay.covered_sources.empty()) return &delay;
  }
  return nullptr;
}

// §32.5: an increment naming its own source adds to the delay in force from
// that source. Where the source has an entry of its own that is what it adds
// to; where it has none, the delay in force is whatever the load's all-sources
// entry carries, so the new source-specific entry starts from that rather than
// from nothing. Adding to nothing would make an increment written after a PORT
// entry read as though the PORT entry had never been there.
void IncrementInterconnectDelayFromSource(
    std::vector<InterconnectDelay>& delays, const InterconnectDelay& delta) {
  for (auto& existing : delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port) {
      AddInterconnectDelayValues(existing, delta);
      return;
    }
  }
  InterconnectDelay seeded = delta;
  if (const auto* base =
          FindAllSourceInterconnectDelay(delays, delta.dst_port)) {
    seeded = *base;
    seeded.src_port = delta.src_port;
    seeded.covered_sources = delta.covered_sources;
    AddInterconnectDelayValues(seeded, delta);
  }
  delays.push_back(std::move(seeded));
}

// §32.5: an increment carrying no source of its own is an increment to the
// delay from every source, so it reaches each entry already standing on that
// load as well as the load's all-sources entry, which it brings into being when
// the load has none. Touching only the all-sources entry would leave a
// source-specific entry holding a value the increment never reached, and that
// entry is the one its source reads.
void IncrementInterconnectDelayFromAllSources(
    std::vector<InterconnectDelay>& delays, const InterconnectDelay& delta) {
  bool has_all_sources = false;
  for (auto& existing : delays) {
    if (existing.dst_port != delta.dst_port) continue;
    AddInterconnectDelayValues(existing, delta);
    if (existing.covered_sources.empty()) has_all_sources = true;
  }
  if (!has_all_sources) delays.push_back(delta);
}

}  // namespace

void SpecifyManager::IncrementInterconnectDelay(
    const InterconnectDelay& delta) {
  if (delta.covered_sources.empty()) {
    IncrementInterconnectDelayFromAllSources(interconnect_delays_, delta);
    return;
  }
  IncrementInterconnectDelayFromSource(interconnect_delays_, delta);
}

void SpecifyManager::AddTimingCheck(TimingCheckEntry check) {
  // §31.2 has each timing check carry its own limits and notifier, and
  // nothing in Clause 31 merges two checks on the same signals, so an entry
  // built from a declaration replaces only the one built from that same
  // declaration in that same instance -- the rebuild
  // RebuildTimingChecksForSpecparam files after an SDF specparam change.
  if (check.decl != nullptr) {
    for (auto& existing : timing_checks_) {
      if (existing.decl == check.decl &&
          existing.inst_prefix == check.inst_prefix) {
        existing = std::move(check);
        return;
      }
    }
    timing_checks_.push_back(std::move(check));
    return;
  }
  for (auto& existing : timing_checks_) {
    // §31.2 puts a system timing check inside a specify block and §30.3 puts
    // that block inside a module declaration, so two instances of one cell
    // declare checks naming identically spelled signals. The instance is
    // compared alongside the signals, or the second instance's check would
    // replace the first instance's rather than stand beside it.
    if (existing.inst_prefix == check.inst_prefix &&
        existing.kind == check.kind &&
        existing.ref_signal == check.ref_signal &&
        existing.ref_select == check.ref_select &&
        existing.ref_edge == check.ref_edge &&
        existing.data_signal == check.data_signal &&
        existing.data_select == check.data_select &&
        existing.data_edge == check.data_edge &&
        SpecifyConditionsMatch(existing.condition, check.condition)) {
      existing = std::move(check);
      return;
    }
  }
  timing_checks_.push_back(std::move(check));
}

namespace {

bool SdfAnnotationMatchesCheck(const TimingCheckEntry& existing,
                               const SdfTcAnnotation& a,
                               std::string_view inst_prefix) {
  // §31.2 puts a system timing check inside a specify block, so two instances
  // of one cell declare checks naming identically spelled signals and the
  // instance is what tells them apart. The prefixes are compared exactly, an
  // empty one naming the module the design was elaborated as rather than every
  // instance: SdfCellPrefixInRegion (simulator/sdf_parser.h) answers a definite
  // prefix for every cell, so no annotation arrives with its instance left
  // unspecified. The SpecifyEdge::kNone and the empty condition below do reach
  // a check carrying any edge or any condition, which is what §32.4.2 rules for
  // an SDF check whose signals the file wrote no edge and no condition on.
  if (existing.inst_prefix != inst_prefix) return false;
  if (existing.kind != a.kind) return false;
  if (existing.ref_signal != a.ref_signal) return false;
  if (existing.data_signal != a.data_signal) return false;
  if (a.ref_edge != SpecifyEdge::kNone && existing.ref_edge != a.ref_edge)
    return false;
  if (a.data_edge != SpecifyEdge::kNone && existing.data_edge != a.data_edge)
    return false;
  if (!a.condition.empty() &&
      !SpecifyConditionsMatch(existing.condition, a.condition)) {
    return false;
  }
  return true;
}

void ApplySdfAnnotationFields(TimingCheckEntry& check,
                              const SdfTcAnnotation& a) {
  if (a.set_limit) check.limit = a.limit;
  if (a.set_limit2) check.limit2 = a.limit2;
  if (a.set_start_edge_offset) check.start_edge_offset = a.start_edge_offset;
  if (a.set_end_edge_offset) check.end_edge_offset = a.end_edge_offset;
}

}  // namespace

bool SpecifyManager::AnnotateSdfTimingCheck(const SdfTcAnnotation& a,
                                            std::string_view inst_prefix) {
  // §32.1: SDF back-annotates the timing checks a design already declares in
  // its specify blocks; it never introduces a new check. A single SDF check
  // (e.g. SETUPHOLD) expands into several candidate annotations (setup, hold,
  // setuphold) so it can update whichever representation the specify block
  // uses; candidates that match nothing are simply dropped, not appended.
  // Appending them would fabricate checks the RTL never declared (turning one
  // SETUPHOLD into three entries).
  bool applied = false;
  for (auto& existing : timing_checks_) {
    if (!SdfAnnotationMatchesCheck(existing, a, inst_prefix)) continue;
    ApplySdfAnnotationFields(existing, a);
    applied = true;
  }
  return applied;
}

void SpecifyManager::AddPrimitiveDriver(PrimitiveDriver driver) {
  primitive_drivers_.push_back(std::move(driver));
}

void SpecifyManager::AddPrimitiveDriversFromGate(const ModuleItem& gate,
                                                 SimContext& ctx, Arena& arena,
                                                 std::string_view inst_prefix) {
  for (auto& driver : BuildPrimitiveDriversFromGate(gate, ctx, arena)) {
    // §28.4 names a gate's terminals by the declaring module's own port names,
    // so the instance is what tells two instances of one cell apart when
    // AnnotateSdfDeviceDelay looks for the primitives driving an output.
    driver.inst_prefix = inst_prefix;
    AddPrimitiveDriver(std::move(driver));
  }
  // §29.8 puts a primitive instance inside a module, so one gate declaration is
  // registered once per instance of the cell holding it and the declaration
  // alone does not identify what was already recorded. The instance travels
  // with it because RebuildGateDriversForSpecparam evaluates the delay
  // expression in, and files the rebuilt driver back at, the instance the
  // declaration came from.
  for (const auto& seen : gate_decls_) {
    if (seen.gate == &gate && seen.inst_prefix == inst_prefix) return;
  }
  gate_decls_.push_back({&gate, std::string(inst_prefix)});
}

namespace {

// Writes an SDF DEVICE entry's twelve values over `slots`, or adds them to what
// is there when the entry came from an INCREMENT delay section.
void ApplySdfDeviceValues(uint64_t (&slots)[12], const SdfDeviceAnnotation& a) {
  for (int i = 0; i < 12; ++i) {
    slots[i] = a.is_increment ? slots[i] + a.delays[i] : a.delays[i];
  }
}

// §32.8: the transition slots whose transition ends at the x state -- 0 to x,
// 1 to x and z to x. A construct that carries only three state transition
// delays has a single delay to the x state, so all three take the same value.
constexpr int kSlotsReachingX[3] = {6, 8, 11};

// §32.8: write an SDF DEVICE entry onto a gate primitive, which is one of the
// constructs that carries three state transition delays rather than twelve. The
// three the entry reduced to spread over the slots the way a three-delay
// declaration spreads, and the delay to the x state -- which the reduction took
// as the smallest of the three -- fills every slot whose transition ends at x,
// in place of whatever that spreading derived there. An INCREMENT entry changes
// what the primitive already carries rather than replacing it, in each of the
// four values it supplies.
void ApplySdfDeviceThreeStateValues(PrimitiveDriver& driver,
                                    const SdfDeviceAnnotation& a) {
  PathDelay scratch;
  scratch.delay_count = 3;
  for (int i = 0; i < 3; ++i) {
    scratch.delays[i] = a.three_state_delays[i];
    if (a.is_increment) scratch.delays[i] += driver.delays[i];
  }
  ExpandTransitionDelays(scratch);

  uint64_t to_x = a.three_state_delays[3];
  if (a.is_increment) to_x += driver.delays[kSlotsReachingX[0]];
  for (int slot : kSlotsReachingX) scratch.delays[slot] = to_x;

  driver.delay_count = 3;
  for (int i = 0; i < 12; ++i) driver.delays[i] = scratch.delays[i];
  driver.sdf_annotated = true;
}

}  // namespace

const PrimitiveDriver* SpecifyManager::FindAnnotatedPrimitiveDriver(
    std::string_view inst_prefix, std::string_view output) const {
  for (const auto& driver : primitive_drivers_) {
    if (driver.sdf_annotated && driver.inst_prefix == inst_prefix &&
        driver.output_port == output) {
      return &driver;
    }
  }
  return nullptr;
}

void SpecifyManager::AnnotateDriverDelays(std::string_view inst_prefix,
                                          std::string_view output,
                                          const uint64_t (&delays)[3]) {
  PrimitiveDriver* driver = nullptr;
  for (auto& candidate : primitive_drivers_) {
    if (candidate.inst_prefix == inst_prefix &&
        candidate.output_port == output) {
      driver = &candidate;
      break;
    }
  }
  if (driver == nullptr) {
    driver = &primitive_drivers_.emplace_back();
    driver->inst_prefix = std::string(inst_prefix);
    driver->output_port = std::string(output);
  }
  driver->delay_count = 3;
  for (int i = 0; i < 3; ++i) driver->delays[i] = delays[i];
  driver->sdf_annotated = true;
}

bool SpecifyManager::AnnotateSdfDeviceDelay(const SdfDeviceAnnotation& a,
                                            std::string_view inst_prefix) {
  // An entry with no operand is the whole-module row: it reaches every specify
  // path, because every specify path ends at a module output. An operand names
  // one output and narrows the entry to it; an operand that names no output
  // this manager knows about -- a submodule instance, whose own declarations
  // live with that submodule -- reaches nothing here.
  const bool kReachesAllOutputs = a.port_instance.empty();

  // §30.3 puts a specify block inside a module declaration, so two instances of
  // one cell hold outputs spelled identically. `inst_prefix` is what
  // SdfCellPrefixInRegion (simulator/sdf_annotate.cpp) made of the entry's
  // CELLINSTANCE, so both scans reach the outputs of that one instance.
  bool applied = false;
  for (auto& pd : path_delays_) {
    if (pd.inst_prefix != inst_prefix) continue;
    if (!kReachesAllOutputs && pd.dst_port != a.port_instance) continue;
    // Only the propagation delays come from the file; each path keeps its own
    // condition, ifnone flag and pulse limits, which a DEVICE entry says
    // nothing about (§32.3).
    ApplySdfDeviceValues(pd.delays, a);
    pd.delay_count = 12;
    applied = true;
  }
  if (applied) return true;

  // No specify path covers the outputs the entry reaches, so the delay belongs
  // to the primitives driving them instead. §32.8: a gate primitive is not a
  // specify path and carries three state transition delays rather than twelve,
  // so the entry's values reach it through the reduction rather than through
  // the twelve-slot expansion the paths above take.
  for (auto& driver : primitive_drivers_) {
    // PrimitiveDriver::inst_prefix is compared for the reason
    // PathDelay::inst_prefix is compared above. RegisterModuleGates
    // (simulator/specify_register.cpp) fills it, once per module instance, from
    // the gate instantiations RtlirModule::gate_insts kept.
    if (driver.inst_prefix != inst_prefix) continue;
    if (!kReachesAllOutputs && driver.output_port != a.port_instance) continue;
    ApplySdfDeviceThreeStateValues(driver, a);
    applied = true;
  }
  return applied;
}

void SpecifyManager::AddPathDelayFromDecl(const SpecifyPathDecl& decl,
                                          SimContext& ctx, Arena& arena,
                                          bool default_pulse_limits,
                                          std::string_view inst_prefix) {
  // §30.4.6 (printed page 880): a full connection declares a path from every
  // source to every destination, and a parallel one the path between its two.
  const bool kFull = decl.path_kind == SpecifyPathKind::kFull;
  const std::size_t kSources =
      kFull ? std::max<std::size_t>(decl.src_ports.size(), 1) : 1;
  const std::size_t kDestinations =
      kFull ? std::max<std::size_t>(decl.dst_ports.size(), 1) : 1;
  for (std::size_t src = 0; src < kSources; ++src) {
    for (std::size_t dst = 0; dst < kDestinations; ++dst) {
      PathDelay pd = BuildPathDelayFromDecl(decl, ctx, arena, src, dst);
      // §30.4 names a path's terminals by the declaring module's own port
      // names, so the instance is what tells two instances of one cell apart.
      pd.inst_prefix = inst_prefix;
      if (default_pulse_limits) InitDefaultPulseLimits(pd);
      // §30.5.3 (printed page 885): every declared path is a path of its own,
      // a second declaration between the same terminals among them, and where
      // more than one is active for a transition the least of their delays is
      // used, so a declaration adds its paths rather than overwriting one it
      // shares terminals, an edge or a condition with. The instance, the entry
      // and the terminals travel with the declaration so
      // RebuildPathDelaysForSpecparam replaces that very entry.
      path_decls_.push_back(
          {&decl, std::string(inst_prefix), path_delays_.size(), src, dst});
      path_delays_.push_back(std::move(pd));
    }
  }
}

void SpecifyManager::BindDesignSpecparams(std::vector<std::string> names,
                                          SimContext& ctx, Arena& arena,
                                          std::string_view inst_prefix) {
  // §32.4.3: the names are added to what is already bound rather than
  // replacing it. RegisterSpecifyBlocks calls this once per module instance
  // that declared a specify block, so replacing would leave only the last
  // instance's specparams annotatable.
  for (auto& name : names) {
    if (IsDeclaredSpecparam(inst_prefix, name)) continue;
    declared_specparams_.push_back({std::string(inst_prefix), std::move(name)});
  }
  specparam_ctx_ = &ctx;
  specparam_arena_ = &arena;
}

bool SpecifyManager::IsDeclaredSpecparam(std::string_view inst_prefix,
                                         std::string_view name) const {
  for (const auto& declared : declared_specparams_) {
    if (declared.inst_prefix == inst_prefix && declared.name == name) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
