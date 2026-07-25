#include "simulator/specify.h"

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
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

namespace {

// The spelling of an operator a state-dependent path condition may be built
// from (§30.4.4.1). An operator with no spelling here is one the condition text
// below cannot render.
std::string_view SpecifyConditionOperator(TokenKind op) {
  switch (op) {
    case TokenKind::kBang:
      return "!";
    case TokenKind::kTilde:
      return "~";
    case TokenKind::kAmpAmp:
      return "&&";
    case TokenKind::kPipePipe:
      return "||";
    case TokenKind::kEqEq:
      return "==";
    case TokenKind::kBangEq:
      return "!=";
    case TokenKind::kEqEqEq:
      return "===";
    case TokenKind::kBangEqEq:
      return "!==";
    case TokenKind::kAmp:
      return "&";
    case TokenKind::kPipe:
      return "|";
    case TokenKind::kCaret:
      return "^";
    default:
      return {};
  }
}

// §32.4.1: render a module path's condition as the text an SDF COND condition
// is compared against. Backannotation matches a conditional delay to a specify
// path by names *and* condition, so the condition a state-dependent path was
// declared with has to travel with the path in a comparable form. A condition
// this cannot spell out yields no text, leaving the path matched on names
// alone, exactly as an unconditional one is.
std::string SpecifyConditionText(const Expr* cond) {
  if (cond == nullptr) return {};
  switch (cond->kind) {
    case ExprKind::kIdentifier:
      return std::string(cond->text);
    case ExprKind::kIntegerLiteral:
      return std::to_string(cond->int_val);
    case ExprKind::kUnary: {
      const std::string_view kOp = SpecifyConditionOperator(cond->op);
      std::string operand = SpecifyConditionText(cond->lhs);
      if (kOp.empty() || operand.empty()) return {};
      return std::string(kOp) + operand;
    }
    case ExprKind::kBinary: {
      const std::string_view kOp = SpecifyConditionOperator(cond->op);
      std::string lhs = SpecifyConditionText(cond->lhs);
      std::string rhs = SpecifyConditionText(cond->rhs);
      if (kOp.empty() || lhs.empty() || rhs.empty()) return {};
      return lhs + " " + std::string(kOp) + " " + rhs;
    }
    default:
      return {};
  }
}

}  // namespace

PathDelay BuildPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                                 Arena& arena) {
  PathDelay pd;
  if (!decl.src_ports.empty()) {
    pd.src_port = std::string(decl.src_ports.front().name);
  }
  if (!decl.dst_ports.empty()) {
    pd.dst_port = std::string(decl.dst_ports.front().name);
  }
  pd.path_kind = decl.path_kind;
  pd.edge = decl.edge;
  pd.is_ifnone = decl.is_ifnone;
  pd.condition = SpecifyConditionText(decl.condition);

  // The parser accepts only the one/two/three/six/twelve delay lists of
  // Syntax 30-6 (§30.5); an empty list defaults to a single typical delay.
  std::size_t count = decl.delays.size();
  if (count > 12) count = 12;
  pd.delay_count = static_cast<uint8_t>(count == 0 ? 1 : count);

  for (std::size_t i = 0; i < count; ++i) {
    // §30.5.1: a single value is the typical delay; a colon-separated
    // min:typ:max triple selects one member. EvalExpr resolves a
    // constant_mintypmax_expression against the context's delay mode.
    Logic4Vec value = EvalExpr(decl.delays[i], ctx, arena);
    const uint32_t kWidth = value.width == 0 ? 64u : value.width;
    const int64_t kSigned = SignExtend(value.ToUint64(), kWidth);
    // §30.5.1: a delay expression that evaluates negative is treated as zero.
    pd.delays[i] = ClampPathDelay(kSigned);
  }

  // §30.5.1 / Table 30-2: distribute the listed delays over the twelve
  // transition slots according to how many were specified.
  ExpandTransitionDelays(pd);
  return pd;
}

std::vector<std::string> CollectDeclaredSpecparams(const ModuleDecl& mod) {
  std::vector<std::string> names;
  auto add = [&names](std::string_view name) {
    if (name.empty()) return;
    for (const auto& seen : names) {
      if (seen == name) return;
    }
    names.emplace_back(name);
  };
  for (const auto* item : mod.items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kSpecparam) {
      add(item->name);
      continue;
    }
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (const auto* si : item->specify_items) {
      if (si != nullptr && si->kind == SpecifyItemKind::kSpecparam) {
        add(si->param_name);
      }
    }
  }
  return names;
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
      for (const auto* el : expr->elements) {
        if (ExprReadsSpecparam(el, specparams)) return true;
      }
      return false;
    case ExprKind::kReplicate:
      if (ExprReadsSpecparam(expr->repeat_count, specparams)) return true;
      for (const auto* el : expr->elements) {
        if (ExprReadsSpecparam(el, specparams)) return true;
      }
      return false;
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

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot) {
  if (candidates.empty()) return 0;

  uint64_t max_time = 0;
  for (const auto& c : candidates) {
    if (c.last_transition_time > max_time) max_time = c.last_transition_time;
  }
  bool have_active = false;
  uint64_t best = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr) continue;
    if (c.last_transition_time != max_time) continue;
    if (!c.condition_true) continue;
    uint64_t d = c.path->delays[transition_slot];
    if (!have_active || d < best) {
      best = d;
      have_active = true;
    }
  }
  return have_active ? best : 0;
}

bool StateDependentPathConditionEnables(Logic4Word condition_lsb) {
  // An unknown (x or z) condition counts as true; otherwise the path is active
  // only when the least-significant bit of the result is 1.
  const bool kUnknown = (condition_lsb.bval & 1u) != 0u;
  if (kUnknown) return true;
  return (condition_lsb.aval & 1u) != 0u;
}

uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum) {
  return std::max(module_path_delay, distributed_delay_sum);
}

PulseClassification ClassifyPulse(uint64_t pulse_width, uint64_t reject_limit,
                                  uint64_t error_limit) {
  if (pulse_width >= error_limit) return PulseClassification::kPropagate;
  if (pulse_width >= reject_limit) return PulseClassification::kForceX;
  return PulseClassification::kReject;
}

uint64_t FilteredPulseLeadingXTime(PulseStyle style, uint64_t detect_time,
                                   uint64_t scheduled_leading_time) {
  return style == PulseStyle::kOnDetect ? detect_time : scheduled_leading_time;
}

bool IsNegativePulse(uint64_t leading_time, uint64_t trailing_time) {
  return trailing_time < leading_time;
}

NegativePulseSchedule ScheduleNegativePulse(ShowCancelled mode,
                                            PulseStyle style,
                                            uint64_t detect_time,
                                            uint64_t scheduled_leading_time) {
  // noshowcancelled: cancel the leading edge with no x indication.
  if (mode == ShowCancelled::kNoshowcancelled) {
    return {/*force_x=*/false, /*x_time=*/0};
  }
  // showcancelled: drive the output to x. The style decides only when the to-x
  // transition is scheduled (on-event replaces the leading edge schedule,
  // on-detect advances it to the detection moment).
  return {/*force_x=*/true, FilteredPulseLeadingXTime(style, detect_time,
                                                      scheduled_leading_time)};
}

void InitDefaultPulseLimits(PathDelay& pd) {
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i];
    pd.error_limit[i] = pd.delays[i];
  }
}

void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error) {
  const uint64_t kEffectiveError = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = kEffectiveError;
  }
}

void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct) {
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
    pd.error_limit[i] = pd.delays[i] * error_pct / 100;
  }
}

void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error) {
  const uint64_t kEffectiveError = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = kEffectiveError;
  }
}

namespace {

// Overwrites `existing` with `replacement` while optionally retaining the
// original pulse (reject/error) limits.
void ReplacePathDelayPreservingPulse(PathDelay& existing, PathDelay replacement,
                                     bool preserve_pulse_limits) {
  uint64_t saved_reject[12];
  uint64_t saved_error[12];
  if (preserve_pulse_limits) {
    for (int i = 0; i < 12; ++i) {
      saved_reject[i] = existing.reject_limit[i];
      saved_error[i] = existing.error_limit[i];
    }
  }
  existing = std::move(replacement);
  if (preserve_pulse_limits) {
    for (int i = 0; i < 12; ++i) {
      existing.reject_limit[i] = saved_reject[i];
      existing.error_limit[i] = saved_error[i];
    }
  }
}

// Nonconditional SDF update: overwrites every existing path delay between the
// same ports, but keeps each entry's original condition/ifnone (and optionally
// its pulse limits). Returns true if at least one entry matched.
bool UpdateNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                    const PathDelay& delay,
                                    bool preserve_pulse_limits) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port) {
      std::string saved_cond = existing.condition;
      bool saved_ifnone = existing.is_ifnone;
      ReplacePathDelayPreservingPulse(existing, delay, preserve_pulse_limits);
      existing.condition = std::move(saved_cond);
      existing.is_ifnone = saved_ifnone;
      matched = true;
    }
  }
  return matched;
}

}  // namespace

void SpecifyManager::AddPathDelay(PathDelay delay, bool preserve_pulse_limits) {
  const bool kSdfIsNonconditional = delay.condition.empty() && !delay.is_ifnone;
  if (kSdfIsNonconditional) {
    if (!UpdateNonconditionalPathDelays(path_delays_, delay,
                                        preserve_pulse_limits)) {
      path_delays_.push_back(std::move(delay));
    }
    return;
  }
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.condition == delay.condition &&
        existing.is_ifnone == delay.is_ifnone) {
      ReplacePathDelayPreservingPulse(existing, std::move(delay),
                                      preserve_pulse_limits);
      return;
    }
  }
  path_delays_.push_back(std::move(delay));
}

bool SpecifyManager::AnnotateSdfPathDelay(PathDelay delay,
                                          bool preserve_pulse_limits) {
  const bool kSdfIsNonconditional = delay.condition.empty() && !delay.is_ifnone;
  if (kSdfIsNonconditional) {
    // §32.4.1: a nonconditional entry reaches all paths between those two
    // ports. Its rule names no restriction to paths already declared, so an
    // entry matching none is still kept, which is how §32.3 chose to hold on to
    // delay data that finds no home.
    if (!UpdateNonconditionalPathDelays(path_delays_, delay,
                                        preserve_pulse_limits)) {
      path_delays_.push_back(std::move(delay));
    }
    return true;
  }
  // §32.4.1: a conditional entry may land *only* on a path between those same
  // two ports carrying the same condition. Where the module declares no such
  // path there is nothing for it to annotate, so it lands nowhere. Appending
  // one instead would conjure up a specify path the design never wrote, and
  // backannotation only ever updates what a design already declares.
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.condition == delay.condition &&
        existing.is_ifnone == delay.is_ifnone) {
      ReplacePathDelayPreservingPulse(existing, std::move(delay),
                                      preserve_pulse_limits);
      return true;
    }
  }
  return false;
}

namespace {

void AddPathDelayValues(PathDelay& existing, const PathDelay& delta) {
  for (int i = 0; i < 12; ++i) existing.delays[i] += delta.delays[i];
}

// Adds `delta` to every existing path delay between the same ports (ignoring
// condition/ifnone). Returns true if at least one entry matched.
bool IncrementNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                       const PathDelay& delta) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port) {
      AddPathDelayValues(existing, delta);
      matched = true;
    }
  }
  return matched;
}

// Adds `delta` to the first existing path delay matching ports plus
// condition/ifnone. Returns true if a matching entry was found.
bool IncrementConditionalPathDelay(std::vector<PathDelay>& path_delays,
                                   const PathDelay& delta) {
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port &&
        existing.condition == delta.condition &&
        existing.is_ifnone == delta.is_ifnone) {
      AddPathDelayValues(existing, delta);
      return true;
    }
  }
  return false;
}

}  // namespace

void SpecifyManager::IncrementPathDelay(const PathDelay& delta) {
  const bool kSdfIsNonconditional = delta.condition.empty() && !delta.is_ifnone;
  const bool kMatched =
      kSdfIsNonconditional
          ? IncrementNonconditionalPathDelays(path_delays_, delta)
          : IncrementConditionalPathDelay(path_delays_, delta);
  if (!kMatched) path_delays_.push_back(delta);
}

bool SpecifyManager::IncrementSdfPathDelay(const PathDelay& delta) {
  const bool kSdfIsNonconditional = delta.condition.empty() && !delta.is_ifnone;
  if (kSdfIsNonconditional) {
    if (!IncrementNonconditionalPathDelays(path_delays_, delta)) {
      path_delays_.push_back(delta);
    }
    return true;
  }
  // §32.4.1, as above: with no declared path carrying that condition there is
  // nothing to add to.
  return IncrementConditionalPathDelay(path_delays_, delta);
}

void SpecifyManager::IncrementInterconnectDelay(
    const InterconnectDelay& delta) {
  for (auto& existing : interconnect_delays_) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port) {
      existing.rise += delta.rise;
      existing.fall += delta.fall;
      for (int i = 0; i < 12; ++i) {
        existing.delays[i] += delta.delays[i];
      }
      return;
    }
  }
  interconnect_delays_.push_back(delta);
}

void SpecifyManager::AddTimingCheck(TimingCheckEntry check) {
  for (auto& existing : timing_checks_) {
    if (existing.kind == check.kind &&
        existing.ref_signal == check.ref_signal &&
        existing.ref_edge == check.ref_edge &&
        existing.data_signal == check.data_signal &&
        existing.data_edge == check.data_edge &&
        existing.condition == check.condition) {
      existing = std::move(check);
      return;
    }
  }
  timing_checks_.push_back(std::move(check));
}

namespace {

bool SdfAnnotationMatchesCheck(const TimingCheckEntry& existing,
                               const SdfTcAnnotation& a) {
  if (existing.kind != a.kind) return false;
  if (existing.ref_signal != a.ref_signal) return false;
  if (existing.data_signal != a.data_signal) return false;
  if (a.ref_edge != SpecifyEdge::kNone && existing.ref_edge != a.ref_edge)
    return false;
  if (a.data_edge != SpecifyEdge::kNone && existing.data_edge != a.data_edge)
    return false;
  if (!a.condition.empty() && existing.condition != a.condition) return false;
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

bool SpecifyManager::AnnotateSdfTimingCheck(const SdfTcAnnotation& a) {
  // §32.1: SDF back-annotates the timing checks a design already declares in
  // its specify blocks; it never introduces a new check. A single SDF check
  // (e.g. SETUPHOLD) expands into several candidate annotations (setup, hold,
  // setuphold) so it can update whichever representation the specify block
  // uses; candidates that match nothing are simply dropped, not appended.
  // Appending them would fabricate checks the RTL never declared (turning one
  // SETUPHOLD into three entries).
  bool applied = false;
  for (auto& existing : timing_checks_) {
    if (!SdfAnnotationMatchesCheck(existing, a)) continue;
    ApplySdfAnnotationFields(existing, a);
    applied = true;
  }
  return applied;
}

void SpecifyManager::AddPrimitiveDriver(PrimitiveDriver driver) {
  primitive_drivers_.push_back(std::move(driver));
}

void SpecifyManager::AddPrimitiveDriversFromGate(const ModuleItem& gate,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  for (auto& driver : BuildPrimitiveDriversFromGate(gate, ctx, arena)) {
    AddPrimitiveDriver(std::move(driver));
  }
  for (const auto* seen : gate_decls_) {
    if (seen == &gate) return;
  }
  gate_decls_.push_back(&gate);
}

namespace {

// Writes an SDF DEVICE entry's twelve values over `slots`, or adds them to what
// is there when the entry came from an INCREMENT delay section.
void ApplySdfDeviceValues(uint64_t (&slots)[12], const SdfDeviceAnnotation& a) {
  for (int i = 0; i < 12; ++i) {
    slots[i] = a.is_increment ? slots[i] + a.delays[i] : a.delays[i];
  }
}

}  // namespace

bool SpecifyManager::AnnotateSdfDeviceDelay(const SdfDeviceAnnotation& a) {
  // An entry with no operand is the whole-module row: it reaches every specify
  // path, because every specify path ends at a module output. An operand names
  // one output and narrows the entry to it; an operand that names no output
  // this manager knows about -- a submodule instance, whose own declarations
  // live with that submodule -- reaches nothing here.
  const bool kReachesAllOutputs = a.port_instance.empty();

  bool applied = false;
  for (auto& pd : path_delays_) {
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
  // to the primitives driving them instead.
  for (auto& driver : primitive_drivers_) {
    if (!kReachesAllOutputs && driver.output_port != a.port_instance) continue;
    ApplySdfDeviceValues(driver.delays, a);
    driver.delay_count = 12;
    applied = true;
  }
  return applied;
}

void SpecifyManager::AnnotateSdf(SdfAnnotation annotation) {
  sdf_annotations_.push_back(std::move(annotation));
}

void SpecifyManager::AddPathDelayFromDecl(const SpecifyPathDecl& decl,
                                          SimContext& ctx, Arena& arena) {
  AddPathDelay(BuildPathDelayFromDecl(decl, ctx, arena));
  path_decls_.push_back(&decl);
}

void SpecifyManager::BindDesignSpecparams(std::vector<std::string> names,
                                          SimContext& ctx, Arena& arena) {
  declared_specparams_ = std::move(names);
  specparam_ctx_ = &ctx;
  specparam_arena_ = &arena;
}

bool SpecifyManager::IsDeclaredSpecparam(std::string_view name) const {
  for (const auto& declared : declared_specparams_) {
    if (declared == name) return true;
  }
  return false;
}

void SpecifyManager::ApplyAnnotatedSpecparam(const std::string& name,
                                             uint64_t value) {
  if (specparam_ctx_ == nullptr) return;
  // §32.4.3: a LABEL section annotates to specparams. A name the module did not
  // declare as a specparam therefore has nothing here for the annotation to
  // land on, whatever else the design may happen to call by that name.
  if (!IsDeclaredSpecparam(name)) return;

  if (Variable* storage = specparam_ctx_->FindVariable(name);
      storage != nullptr) {
    const uint32_t kWidth =
        storage->value.width == 0 ? 32u : storage->value.width;
    storage->value = MakeLogic4VecVal(*specparam_arena_, kWidth, value);
  }

  // §32.4.3: an expression containing one or more specparams is reevaluated
  // when a value is annotated to it from an SDF file. A module path delay is
  // such an expression, and it was already reduced to a number when the path
  // was declared, so it has to be recomputed from the declaration rather than
  // left at what the previous specparam value produced. An expression that does
  // not contain the specparam this annotation changed reads nothing new, and
  // recomputing it would discard whatever else had been annotated onto it, so
  // it is left exactly as it stands.
  const std::vector<std::string> kChanged{name};
  for (const auto* decl : path_decls_) {
    bool reads = false;
    for (const auto* delay : decl->delays) {
      if (ExprReadsSpecparam(delay, kChanged)) {
        reads = true;
        break;
      }
    }
    if (!reads) continue;
    AddPathDelay(
        BuildPathDelayFromDecl(*decl, *specparam_ctx_, *specparam_arena_),
        /*preserve_pulse_limits=*/true);
  }

  // §32.4.3: the rule reaches every expression containing the specparam, not
  // only module path delays. A timing check's constraint limits are written as
  // expressions as well, and they were likewise reduced to numbers when the
  // check was declared, so a check whose limit reads the changed specparam is
  // rebuilt from its declaration too.
  for (const auto* decl : timing_check_decls_) {
    bool reads = false;
    for (const auto* limit : decl->limits) {
      if (ExprReadsSpecparam(limit, kChanged)) {
        reads = true;
        break;
      }
    }
    if (!reads) continue;
    AddTimingCheck(BuildTimingCheckUnderOptions(
        *decl, *specparam_ctx_, *specparam_arena_, timing_check_options_));
  }

  // §32.4.3: a gate primitive's declared propagation delay is an expression as
  // well, and it too was reduced to numbers when the gate's drivers were
  // registered. A gate whose delay expression reads the changed specparam is
  // rebuilt from its declaration, overwriting the driver already recorded for
  // each output so a DEVICE delay still finds one entry per output rather than
  // a stale one beside a fresh one.
  for (const auto* gate : gate_decls_) {
    const Expr* const kDelays[3] = {gate->gate_delay, gate->gate_delay_fall,
                                    gate->gate_delay_decay};
    bool reads = false;
    for (const Expr* delay : kDelays) {
      if (ExprReadsSpecparam(delay, kChanged)) {
        reads = true;
        break;
      }
    }
    if (!reads) continue;
    for (auto& rebuilt : BuildPrimitiveDriversFromGate(*gate, *specparam_ctx_,
                                                       *specparam_arena_)) {
      bool replaced = false;
      for (auto& existing : primitive_drivers_) {
        if (existing.output_port == rebuilt.output_port) {
          existing = rebuilt;
          replaced = true;
          break;
        }
      }
      if (!replaced) primitive_drivers_.push_back(std::move(rebuilt));
    }
  }
}

void SpecifyManager::SetSpecparamValue(SpecparamValue spec) {
  std::string name = spec.name;
  uint64_t value = spec.value;
  auto it = specparam_index_.find(spec.name);
  if (it != specparam_index_.end()) {
    specparam_values_[it->second] = std::move(spec);
  } else {
    specparam_index_[spec.name] = specparam_values_.size();
    specparam_values_.push_back(std::move(spec));
  }

  ApplyAnnotatedSpecparam(name, value);

  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(value);
  }
}

void SpecifyManager::IncrementSpecparamValue(SpecparamValue delta) {
  std::string name = std::move(delta.name);
  uint64_t added = delta.value;
  uint64_t new_value = added;
  auto it = specparam_index_.find(name);
  if (it != specparam_index_.end()) {
    new_value = specparam_values_[it->second].value + added;
    specparam_values_[it->second].value = new_value;
  } else {
    specparam_index_[name] = specparam_values_.size();
    SpecparamValue stored;
    stored.name = name;
    stored.value = added;
    specparam_values_.push_back(std::move(stored));
  }
  ApplyAnnotatedSpecparam(name, new_value);
  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(new_value);
  }
}

void SpecifyManager::RegisterSpecparamReevaluation(
    std::string name, std::function<void(uint64_t)> reevaluate) {
  specparam_reevaluators_.emplace_back(std::move(name), std::move(reevaluate));
}

namespace {

void ApplySdfPercentPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                                uint64_t error) {
  uint64_t reject_pct = reject;
  uint64_t error_pct = has_error ? error : reject;
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
    pd.error_limit[i] = pd.delays[i] * error_pct / 100;
  }
}

void ClampPulseLimitsToDelays(PathDelay& pd) {
  for (int i = 0; i < 12; ++i) {
    if (pd.reject_limit[i] > pd.delays[i]) pd.reject_limit[i] = pd.delays[i];
    if (pd.error_limit[i] > pd.delays[i]) pd.error_limit[i] = pd.delays[i];
  }
}

}  // namespace

void SpecifyManager::AddSdfPulseLimit(const SdfPulseLimitSpec& spec) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != spec.src || pd.dst_port != spec.dst) continue;
    if (spec.is_percent) {
      ApplySdfPercentPulseLimits(pd, spec.reject, spec.has_error, spec.error);
    } else {
      ApplySdfPulseLimits(pd, spec.reject, spec.has_error, spec.error);
    }
    ClampPulseLimitsToDelays(pd);
  }
}

void SpecifyManager::ResolvePulseControlSpecparams(
    const std::vector<PulseControlSpecparam>& specs) {
  // §30.7.1 precedence: apply every non-path-specific PATHPULSE$ first so it
  // reaches all module paths, then let each path-specific PATHPULSE$in$out
  // override the path it names. Because the path-specific pass runs second, it
  // always wins for the paths it names no matter where the module-wide
  // specparam appeared in source. A path-specific specparam that names no
  // existing path (e.g. a non-first terminal of a multiple-path declaration)
  // matches nothing and is thereby ignored.
  for (const auto& s : specs) {
    if (!s.input.empty() || !s.output.empty()) continue;
    for (auto& pd : path_delays_) {
      ApplyPulseControlOverride(pd, s.reject, s.has_error, s.error);
    }
  }
  for (const auto& s : specs) {
    if (s.input.empty() && s.output.empty()) continue;
    for (auto& pd : path_delays_) {
      if (s.input == std::string_view(pd.src_port) &&
          s.output == std::string_view(pd.dst_port)) {
        ApplyPulseControlOverride(pd, s.reject, s.has_error, s.error);
      }
    }
  }
}

void SpecifyManager::IncrementSdfPulseLimit(std::string_view src,
                                            std::string_view dst,
                                            int64_t reject_delta,
                                            bool has_error,
                                            int64_t error_delta) {
  const int64_t kEffectiveErrorDelta = has_error ? error_delta : reject_delta;
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    for (int i = 0; i < 12; ++i) {
      const int64_t kNewReject =
          static_cast<int64_t>(pd.reject_limit[i]) + reject_delta;
      const int64_t kNewError =
          static_cast<int64_t>(pd.error_limit[i]) + kEffectiveErrorDelta;
      pd.reject_limit[i] =
          kNewReject < 0 ? 0u : static_cast<uint64_t>(kNewReject);
      pd.error_limit[i] = kNewError < 0 ? 0u : static_cast<uint64_t>(kNewError);
    }
  }
}

void SpecifyManager::SetGlobalPulseLimitPercents(uint8_t reject_pct,
                                                 uint8_t error_pct) {
  reject_pulse_pct_ = reject_pct;
  error_pulse_pct_ = error_pct;
}

void SpecifyManager::SetPathOutputPulseStyle(std::string output,
                                             PulseStyle style) {
  path_output_pulse_styles_[std::move(output)] = style;
}

void SpecifyManager::SetGlobalPulseStyle(PulseStyle style) {
  has_global_pulse_style_ = true;
  global_pulse_style_ = style;
}

PulseStyle SpecifyManager::ResolvePulseStyle(std::string_view output) const {
  // The invocation option, when present, overrides every specify block
  // declaration.
  if (has_global_pulse_style_) return global_pulse_style_;
  auto it = path_output_pulse_styles_.find(std::string(output));
  if (it != path_output_pulse_styles_.end()) return it->second;
  // Absent both, the default filtering style is on-event.
  return PulseStyle::kOnEvent;
}

void SpecifyManager::SetPathOutputShowCancelled(std::string output,
                                                ShowCancelled mode) {
  path_output_showcancelled_[std::move(output)] = mode;
}

void SpecifyManager::SetGlobalShowCancelled(ShowCancelled mode) {
  has_global_showcancelled_ = true;
  global_showcancelled_ = mode;
}

ShowCancelled SpecifyManager::ResolveShowCancelled(
    std::string_view output) const {
  // The invocation option, when present, overrides every specify block
  // declaration.
  if (has_global_showcancelled_) return global_showcancelled_;
  auto it = path_output_showcancelled_.find(std::string(output));
  if (it != path_output_showcancelled_.end()) return it->second;
  // Absent both, the default is noshowcancelled.
  return ShowCancelled::kNoshowcancelled;
}

void SpecifyManager::AddInterconnectDelay(InterconnectDelay delay) {
  if (delay.src_port.empty()) {
    interconnect_delays_.erase(
        std::remove_if(interconnect_delays_.begin(), interconnect_delays_.end(),
                       [&](const InterconnectDelay& existing) {
                         return existing.dst_port == delay.dst_port;
                       }),
        interconnect_delays_.end());
    interconnect_delays_.push_back(std::move(delay));
    return;
  }

  for (auto& existing : interconnect_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port) {
      existing = std::move(delay);
      return;
    }
  }
  interconnect_delays_.push_back(std::move(delay));
}

uint64_t SpecifyManager::GetPathDelay(std::string_view src,
                                      std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) {
      return pd.delays[0];
    }
  }
  return 0;
}

bool SpecifyManager::HasPathDelay(std::string_view src,
                                  std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) return true;
  }
  return false;
}

bool SpecifyManager::CheckSetupViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         std::string_view data,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSetup) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckHoldViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kHold) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

bool SpecifyManager::CheckRemovalViolation(std::string_view ref,
                                           uint64_t ref_time,
                                           std::string_view data,
                                           uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRemoval) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckRecoveryViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRecovery) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

// Shared implementation for the two-sided timing checks (recrem / setuphold).
// Both checks share an identical structure: filter by kind/signals, handle the
// negative-timing-check window, then compare the elapsed time against a pair of
// limits. The only behavioral difference is which limit applies on each side of
// the reference time: recrem uses limit2 for the "before" side and limit for
// the "after" side, while setuphold uses the opposite. `lower_side_limit`
// selects which member is compared when data_time <= ref_time, and
// `upper_side_limit` when data_time > ref_time.
namespace {

// A single observed reference/data transition pair to test against the timing
// checks (IEEE 1800 §31): the reference event (signal + time) and the data
// event (signal + time) that together describe one timing-check observation.
struct TimingCheckEvent {
  std::string_view ref;
  uint64_t ref_time;
  std::string_view data;
  uint64_t data_time;
};

// Selects which TimingCheckEntry limit applies on each side of the reference
// time for two-sided checks (recrem / setuphold): `lower` is compared when the
// data event is on/before the reference, `upper` when it is after.
struct TwoSidedLimitSelector {
  uint64_t TimingCheckEntry::* lower;
  uint64_t TimingCheckEntry::* upper;
};

// True when `data_time` falls inside the negative-timing-check window centered
// on `ref_time` and spanning [-signed_limit, +signed_limit2].
bool NegativeTimingWindowViolated(const TimingCheckEntry& check,
                                  uint64_t ref_time, uint64_t data_time) {
  const auto kRefT = static_cast<int64_t>(ref_time);
  const auto kDataT = static_cast<int64_t>(data_time);
  const int64_t kLower = kRefT - check.signed_limit;
  const int64_t kUpper = kRefT + check.signed_limit2;
  return kDataT > kLower && kDataT < kUpper;
}

// True when the elapsed time between `ref_time` and `data_time` violates the
// side-specific limit (lower side for data on/before ref, upper side after).
bool TwoSidedLimitViolated(const TimingCheckEntry& check, uint64_t ref_time,
                           uint64_t data_time,
                           uint64_t TimingCheckEntry::* lower_side_limit,
                           uint64_t TimingCheckEntry::* upper_side_limit) {
  if (check.limit == 0 && check.limit2 == 0) return false;
  if (data_time <= ref_time) {
    return ref_time - data_time < check.*lower_side_limit;
  }
  return data_time - ref_time < check.*upper_side_limit;
}

}  // namespace

static bool CheckTimingViolation(
    const std::vector<TimingCheckEntry>& timing_checks, TimingCheckKind kind,
    const TimingCheckEvent& event, const TwoSidedLimitSelector& selector) {
  for (const auto& check : timing_checks) {
    if (check.kind != kind) continue;
    if (check.ref_signal != event.ref) continue;
    if (check.data_signal != event.data) continue;
    if (check.negative_timing_check_enabled) {
      if (NegativeTimingWindowViolated(check, event.ref_time, event.data_time))
        return true;
      continue;
    }
    if (TwoSidedLimitViolated(check, event.ref_time, event.data_time,
                              selector.lower, selector.upper)) {
      return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckRecremViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          std::string_view data,
                                          uint64_t data_time) const {
  // §31.9.4: the option that switches all timing checks off suppresses this
  // check the same way it suppresses $setuphold.
  if (timing_check_options_.all_timing_checks_off) return false;
  return CheckTimingViolation(
      timing_checks_, TimingCheckKind::kRecrem,
      {ref, ref_time, data, data_time},
      {&TimingCheckEntry::limit2, &TimingCheckEntry::limit});
}

bool SpecifyManager::CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSkew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckTimeskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kTimeskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

namespace {

bool FullskewWindowViolated(const TimingCheckEntry& check, uint64_t ref_time,
                            uint64_t data_time) {
  if (ref_time < data_time) {
    return data_time - ref_time > check.limit;
  }
  if (data_time < ref_time) {
    return ref_time - data_time > check.limit2;
  }
  return false;
}

}  // namespace

bool SpecifyManager::CheckFullskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kFullskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (FullskewWindowViolated(check, ref_time, data_time)) return true;
  }
  return false;
}

bool SpecifyManager::CheckWidthViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kWidth) continue;
    if (check.ref_signal != ref) continue;

    if (data_time <= ref_time) continue;
    uint64_t elapsed = data_time - ref_time;

    if (elapsed > check.threshold && elapsed < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckNochangeViolation(std::string_view ref,
                                            uint64_t leading_ref_time,
                                            uint64_t trailing_ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kNochange) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    int64_t begin =
        static_cast<int64_t>(leading_ref_time) - check.start_edge_offset;
    int64_t end =
        static_cast<int64_t>(trailing_ref_time) + check.end_edge_offset;
    auto t = static_cast<int64_t>(data_time);

    if (begin < t && t < end) return true;
  }
  return false;
}

bool SpecifyManager::CheckPeriodViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kPeriod) continue;
    if (check.ref_signal != ref) continue;

    if (data_time <= ref_time) continue;

    if (data_time - ref_time < check.limit) return true;
  }
  return false;
}

bool ReportsFullskewViolation(uint64_t timestamp_time, uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= timestamp_time) return false;
  uint64_t elapsed = next_event_time - timestamp_time;
  if (event_based_flag) {
    return next_event_is_timecheck && elapsed > limit;
  }

  return elapsed > limit;
}

FullskewWindowAction FullskewSecondTimestampAction(
    bool timestamp_condition_holds, bool remain_active_flag) {
  // A timestamp whose condition holds (or that carries no condition) always
  // opens a fresh timing window, superseding any window in progress and
  // re-arming the check if it was dormant.
  if (timestamp_condition_holds) return FullskewWindowAction::kReplaceWindow;

  // With a false condition the remain_active_flag is decisive: when set, the
  // event is discarded and the existing window stands; when clear, the check
  // turns dormant.
  if (remain_active_flag) return FullskewWindowAction::kIgnore;
  return FullskewWindowAction::kGoDormant;
}

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= ref_time) return false;
  uint64_t elapsed = next_event_time - ref_time;
  if (event_based_flag) {
    return next_event_is_data && elapsed > limit;
  }

  return elapsed > limit;
}

Logic4Word ToggleNotifierOnViolation(Logic4Word current) {
  const bool kPreA = (current.aval & 1u) != 0u;
  const bool kPreB = (current.bval & 1u) != 0u;
  Logic4Word result;
  if (kPreA && kPreB) {
    result.aval = 1u;
    result.bval = 1u;
  } else if (kPreB || kPreA) {
    result.aval = 0u;
    result.bval = 0u;
  } else {
    result.aval = 1u;
    result.bval = 0u;
  }
  return result;
}

bool IsDeterministicTimingCheckCondition(TimingCheckConditionKind kind) {
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
    case TimingCheckConditionKind::kNegate:
    case TimingCheckConditionKind::kCaseEq:
    case TimingCheckConditionKind::kCaseNeq:
      return true;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kNeq:
      return false;
  }
  return false;
}

bool TimingCheckConditionEnables(TimingCheckConditionKind kind,
                                 Logic4Word conditioning_lsb,
                                 uint8_t scalar_constant_bit) {
  const bool kNown = (conditioning_lsb.bval & 1u) == 0u;
  if (!kNown) {
    return !IsDeterministicTimingCheckCondition(kind);
  }
  const auto kBit = static_cast<uint8_t>(conditioning_lsb.aval & 1u);
  const auto kRhs = static_cast<uint8_t>(scalar_constant_bit & 1u);
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
      return kBit == 1u;
    case TimingCheckConditionKind::kNegate:
      return kBit == 0u;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kCaseEq:
      return kBit == kRhs;
    case TimingCheckConditionKind::kNeq:
    case TimingCheckConditionKind::kCaseNeq:
      return kBit != kRhs;
  }
  return false;
}

TimingCheckConditionClass ClassifyTimingCheckCondition(const Expr* condition) {
  TimingCheckConditionClass result;
  if (condition == nullptr) return result;  // unconditioned event -> plain

  // `~ expression`: the bitwise-negation form of scalar_timing_check_condition.
  if (condition->kind == ExprKind::kUnary &&
      condition->op == TokenKind::kTilde) {
    result.kind = TimingCheckConditionKind::kNegate;
    return result;
  }

  // `expression <op> scalar_constant`: the four comparison forms. The LSB of
  // the right-hand scalar_constant is the value compared against.
  if (condition->kind == ExprKind::kBinary) {
    bool matched = true;
    switch (condition->op) {
      case TokenKind::kEqEq:
        result.kind = TimingCheckConditionKind::kEq;
        break;
      case TokenKind::kEqEqEq:
        result.kind = TimingCheckConditionKind::kCaseEq;
        break;
      case TokenKind::kBangEq:
        result.kind = TimingCheckConditionKind::kNeq;
        break;
      case TokenKind::kBangEqEq:
        result.kind = TimingCheckConditionKind::kCaseNeq;
        break;
      default:
        matched = false;
        break;
    }
    if (matched) {
      if (condition->rhs != nullptr) {
        result.scalar_constant_bit =
            static_cast<uint8_t>(condition->rhs->int_val & 1u);
      }
      return result;
    }
  }

  // Any other expression is the plain form: its own value gates the check.
  return result;
}

bool IsSingleSignalTimingCheck(TimingCheckKind kind) {
  return kind == TimingCheckKind::kWidth || kind == TimingCheckKind::kPeriod;
}

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode) {
  if (mode == TimingCheckVectorMode::kSingle) return 1u;

  if (IsSingleSignalTimingCheck(kind)) {
    return static_cast<uint64_t>(ref_width);
  }
  return static_cast<uint64_t>(ref_width) * static_cast<uint64_t>(data_width);
}

uint32_t VectorTransitionViolationCount(uint64_t before, uint64_t after,
                                        uint32_t width) {
  if (width == 0) return 0u;
  // Mask off any bits beyond the vector width, then count the positions whose
  // value differs -- each is one single-bit transition, hence one violation.
  const uint64_t mask =
      (width >= 64u) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1u);
  uint64_t changed = (before ^ after) & mask;
  uint32_t count = 0;
  while (changed != 0) {
    changed &= (changed - 1u);
    ++count;
  }
  return count;
}

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kPeriod:
    case TimingCheckKind::kNochange:
      return true;

    case TimingCheckKind::kSkew:
    case TimingCheckKind::kFullskew:
    case TimingCheckKind::kTimeskew:
      return false;
  }
  return false;
}

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit) {
  if (adjusted_limit <= 0) {
    return {0u, true};
  }
  return {static_cast<uint64_t>(adjusted_limit), false};
}

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks) {
  if (upper <= lower) return false;

  const int64_t kMinWidth = 2 * static_cast<int64_t>(precision_ticks);
  return (upper - lower) >= kMinWidth;
}

uint64_t LatchedNegativeTimingWindowValue(int64_t window_lower,
                                          int64_t window_upper,
                                          int64_t data_transition_time,
                                          uint64_t old_value,
                                          uint64_t new_value) {
  (void)window_upper;
  // The new value is stable across the excluded-endpoint interior only when the
  // data has already settled by the time the window opens; a change at or after
  // the open boundary leaves the old value as the stable (and, inside the
  // window, incorrectly clocked) one.
  return data_transition_time <= window_lower ? new_value : old_value;
}

bool ImplicitDelayedSignalsRequired(bool negative_setup_or_hold_present,
                                    bool explicit_delayed_signals_declared) {
  return negative_setup_or_hold_present && !explicit_delayed_signals_declared;
}

uint64_t EffectiveOutputDelayWithTimingCheckSignalDelay(
    uint64_t propagation_delay, uint64_t timing_check_signal_delay) {
  return timing_check_signal_delay > propagation_delay
             ? timing_check_signal_delay
             : propagation_delay;
}

std::vector<ResolvedDelayedSignal> ResolveDelayedSignals(
    const std::vector<std::pair<std::string, std::string>>& refs) {
  std::vector<ResolvedDelayedSignal> resolved;
  for (const auto& [signal, delayed_name] : refs) {
    ResolvedDelayedSignal* existing = nullptr;
    for (auto& entry : resolved) {
      if (entry.signal == signal) {
        existing = &entry;
        break;
      }
    }
    if (existing == nullptr) {
      // First time this signal is seen: one copy, explicit if declared here.
      resolved.push_back({signal, delayed_name, !delayed_name.empty()});
      continue;
    }
    // The signal already has its single shared copy. If this check supplies an
    // explicit name and the copy is still implicit, promote it -- an explicit
    // declaration in any referencing check is used for all of them.
    if (!existing->is_explicit && !delayed_name.empty()) {
      existing->delayed_name = delayed_name;
      existing->is_explicit = true;
    }
  }
  return resolved;
}

bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits) {
  size_t best_index = limits.size();
  for (size_t i = 0; i < limits.size(); ++i) {
    if (limits[i] >= 0) continue;
    if (best_index == limits.size() || limits[i] > limits[best_index]) {
      best_index = i;
    }
  }
  if (best_index == limits.size()) return false;
  limits[best_index] = 0;
  return true;
}

NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }

  if (signed_setup < 0) return NegativeTimingConditionRole::kRef;

  if (signed_hold < 0) return NegativeTimingConditionRole::kData;

  return NegativeTimingConditionRole::kBoth;
}

NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }
  if (signed_setup < 0) return NegativeTimingConditionRole::kData;
  if (signed_hold < 0) return NegativeTimingConditionRole::kRef;
  return NegativeTimingConditionRole::kBoth;
}

bool OperandGetsImplicitDelayedCopy(TimingCheckOperandKind kind) {
  return kind == TimingCheckOperandKind::kReference ||
         kind == TimingCheckOperandKind::kData;
}

// §31.9.3: the notifier follows the delayed-signal/adjusted-limit verdict. The
// undelayed-input/original-limit verdict is deliberately unused: detection is
// delayed along with the signals, so the toggle happens at the delayed moment.
bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool) {
  return delayed_adjusted_violation;
}

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled) {
  return negative_timing_check_option_enabled && !all_timing_checks_disabled;
}

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active) {
  if (!negative_timing_option_active) return 0;
  return requested_delay;
}

bool NegativeTimingCheckValuesAccepted(
    bool negative_value_present, const TimingCheckInvocationOptions& options) {
  return negative_value_present &&
         NegativeTimingCheckOptionActive(options.negative_timing_checks,
                                         options.all_timing_checks_off);
}

EffectiveDelayedSignals ResolveDelayedSignalsUnderOptions(
    const TimingCheckDecl& decl, int64_t requested_ref_delay,
    int64_t requested_data_delay, const TimingCheckInvocationOptions& options) {
  const bool kActive = NegativeTimingCheckOptionActive(
      options.negative_timing_checks, options.all_timing_checks_off);

  const std::string kRefOriginal(decl.ref_terminal.name);
  const std::string kDataOriginal(decl.data_terminal.name);

  EffectiveDelayedSignals out;
  out.are_copies_of_originals = !kActive;
  if (!kActive) {
    // The model may still declare delayed signals; run without the enabling
    // option they carry the original values, undelayed.
    out.ref_signal = kRefOriginal;
    out.data_signal = kDataOriginal;
    out.ref_delay = EffectiveTimingCheckSignalDelay(requested_ref_delay, false);
    out.data_delay =
        EffectiveTimingCheckSignalDelay(requested_data_delay, false);
    return out;
  }

  // Negative-value handling is in force: an explicitly declared delayed signal
  // names the copy the model can also use; otherwise the copy is the internal
  // (unnamed) one of §31.9.1, tracked here under the original signal's name.
  out.ref_signal =
      decl.delayed_ref.empty() ? kRefOriginal : std::string(decl.delayed_ref);
  out.data_signal = decl.delayed_data.empty() ? kDataOriginal
                                              : std::string(decl.delayed_data);
  out.ref_delay = EffectiveTimingCheckSignalDelay(requested_ref_delay, true);
  out.data_delay = EffectiveTimingCheckSignalDelay(requested_data_delay, true);
  return out;
}

namespace {

// Evaluates one timing_check_limit expression to a signed value. An absent
// expression is zero.
int64_t EvalTimingCheckLimit(Expr* limit, SimContext& ctx, Arena& arena) {
  if (limit == nullptr) return 0;
  Logic4Vec value = EvalExpr(limit, ctx, arena);
  const uint32_t kWidth = value.width == 0 ? 64u : value.width;
  return SignExtend(value.ToUint64(), kWidth);
}

// §31.9.4: the unsigned limit a check evaluates with once negative values are
// not being handled. Only the ordinary two-sided treatment is left, where a
// negative value has no meaning and counts as zero.
uint64_t UnhandledNegativeLimit(int64_t signed_limit) {
  return signed_limit < 0 ? 0u : static_cast<uint64_t>(signed_limit);
}

}  // namespace

TimingCheckEntry BuildTimingCheckUnderOptions(
    const TimingCheckDecl& decl, SimContext& ctx, Arena& arena,
    const TimingCheckInvocationOptions& options) {
  TimingCheckEntry entry;
  entry.kind = decl.check_kind;
  entry.ref_signal = std::string(decl.ref_terminal.name);
  entry.ref_edge = decl.ref_edge;
  entry.data_signal = std::string(decl.data_terminal.name);
  entry.data_edge = decl.data_edge;
  entry.notifier = std::string(decl.notifier);

  // §32.4.1: backannotation looks for a timing check of the same type whose
  // names *and* conditions match, so a check declared with a conditioned event
  // (§31.7) carries that condition in comparable form. An SDF timing check
  // names its condition on the reference signal, so that one identifies the
  // check; a condition carried only by the data signal identifies it instead.
  entry.condition = SpecifyConditionText(decl.ref_condition);
  if (entry.condition.empty()) {
    entry.condition = SpecifyConditionText(decl.data_condition);
  }

  const int64_t kFirst = EvalTimingCheckLimit(
      decl.limits.empty() ? nullptr : decl.limits[0], ctx, arena);
  const int64_t kSecond = EvalTimingCheckLimit(
      decl.limits.size() < 2 ? nullptr : decl.limits[1], ctx, arena);

  entry.signed_limit = kFirst;
  entry.signed_limit2 = kSecond;

  // §31.9.4: whether the negative values the declaration carries are handled at
  // all is decided by the invocation option, not by the declaration.
  const bool kNegativePresent = kFirst < 0 || kSecond < 0;
  entry.negative_timing_check_enabled =
      NegativeTimingCheckValuesAccepted(kNegativePresent, options);

  entry.limit = UnhandledNegativeLimit(kFirst);
  entry.limit2 = UnhandledNegativeLimit(kSecond);
  return entry;
}

void SpecifyManager::SetTimingCheckInvocationOptions(
    TimingCheckInvocationOptions options) {
  timing_check_options_ = options;
  ApplyTimingCheckInvocationOptions();
}

void SpecifyManager::ApplyTimingCheckInvocationOptions() {
  if (NegativeTimingCheckOptionActive(
          timing_check_options_.negative_timing_checks,
          timing_check_options_.all_timing_checks_off)) {
    return;
  }
  // §31.9.4: negative values are handled only while the enabling option is in
  // force, however a check came to carry them -- a declaration built earlier,
  // or a limit that arrived by backannotation. Without that option in force
  // every registered check falls back to its ordinary two-sided treatment.
  for (auto& check : timing_checks_) {
    if (!check.negative_timing_check_enabled) continue;
    check.negative_timing_check_enabled = false;
    if (check.signed_limit < 0) {
      check.limit = UnhandledNegativeLimit(check.signed_limit);
    }
    if (check.signed_limit2 < 0) {
      check.limit2 = UnhandledNegativeLimit(check.signed_limit2);
    }
  }
}

void SpecifyManager::AddTimingCheckUnderOptions(const TimingCheckDecl& decl,
                                                SimContext& ctx, Arena& arena) {
  AddTimingCheck(
      BuildTimingCheckUnderOptions(decl, ctx, arena, timing_check_options_));
  // §32.4.3: a timing check limit is an expression too, so keep the declaration
  // in order to recompute it if an SDF LABEL changes a specparam it reads.
  for (const auto* seen : timing_check_decls_) {
    if (seen == &decl) return;
  }
  timing_check_decls_.push_back(&decl);
}

bool SpecifyManager::CheckSetupholdViolation(std::string_view ref,
                                             uint64_t ref_time,
                                             std::string_view data,
                                             uint64_t data_time) const {
  // §31.9.4: with the invocation option that switches all timing checks off,
  // nothing is checked and so no violation is reported.
  if (timing_check_options_.all_timing_checks_off) return false;
  return CheckTimingViolation(
      timing_checks_, TimingCheckKind::kSetuphold,
      {ref, ref_time, data, data_time},
      {&TimingCheckEntry::limit, &TimingCheckEntry::limit2});
}

}  // namespace delta
