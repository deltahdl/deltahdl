#include "simulator/specify.h"

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify_internal.h"
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

}  // namespace

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
  // §30.4.4: SelectModulePathDelay in simulator/module_path_delay.cpp evaluates
  // this condition for §30.5.3's activity test, which the text above cannot
  // answer, being rendered for §32.4.1's SDF COND matching.
  pd.condition_expr = decl.condition;

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

const PathDelay* SelectActivePath(const std::vector<PathCandidate>& candidates,
                                  uint8_t transition_slot) {
  if (candidates.empty()) return nullptr;

  uint64_t max_time = 0;
  for (const auto& c : candidates) {
    if (c.last_transition_time > max_time) max_time = c.last_transition_time;
  }
  const PathDelay* best_path = nullptr;
  uint64_t best = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr) continue;
    if (c.last_transition_time != max_time) continue;
    if (!c.condition_true) continue;
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
  pd.reject_limit_source = PulseLimitSource::kDefault;
  pd.error_limit_source = PulseLimitSource::kDefault;
}

// §30.7: whether a source may set a limit some source already set. A source
// outranked by what already stands leaves it, so applying the three in any
// order settles on the same limits.
static bool PulseLimitSourceWins(PulseLimitSource standing,
                                 PulseLimitSource source) {
  return static_cast<uint8_t>(source) >= static_cast<uint8_t>(standing);
}

// §30.7.1: a PATHPULSE$ specparam sets the limits, and §30.7.2 puts it above
// the global invocation options. SDF annotation outranks it (§30.7.3), so a
// path already annotated keeps what the annotation gave it.
void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error) {
  const uint64_t kEffectiveError = has_error ? error : reject;
  if (PulseLimitSourceWins(pd.reject_limit_source,
                           PulseLimitSource::kPathpulse)) {
    for (int i = 0; i < 12; ++i) pd.reject_limit[i] = reject;
    pd.reject_limit_source = PulseLimitSource::kPathpulse;
  }
  if (PulseLimitSourceWins(pd.error_limit_source,
                           PulseLimitSource::kPathpulse)) {
    for (int i = 0; i < 12; ++i) pd.error_limit[i] = kEffectiveError;
    pd.error_limit_source = PulseLimitSource::kPathpulse;
  }
}

// Derives the twelve reject and error limits from the twelve delays and the
// pulse-limit percentages in effect. §32.4.4 puts interconnect delays under the
// same pulse-limit rules a specify path delay follows, so both derive their
// limits here rather than each carrying its own arithmetic.
void DerivePulseLimitsFromDelays(const uint64_t (&delays)[12],
                                 uint8_t reject_pct, uint8_t error_pct,
                                 uint64_t (&reject_limit)[12],
                                 uint64_t (&error_limit)[12]) {
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    reject_limit[i] = delays[i] * reject_pct / 100;
    error_limit[i] = delays[i] * error_pct / 100;
  }
}

// §30.7.2: the invocation options' percentages, which both a PATHPULSE$
// specparam and an SDF annotation outrank, so a path either of them has already
// set keeps what it was given.
void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct) {
  uint64_t derived_reject[12];
  uint64_t derived_error[12];
  DerivePulseLimitsFromDelays(pd.delays, reject_pct, error_pct, derived_reject,
                              derived_error);
  if (PulseLimitSourceWins(pd.reject_limit_source, PulseLimitSource::kGlobal)) {
    for (int i = 0; i < 12; ++i) pd.reject_limit[i] = derived_reject[i];
    pd.reject_limit_source = PulseLimitSource::kGlobal;
  }
  if (PulseLimitSourceWins(pd.error_limit_source, PulseLimitSource::kGlobal)) {
    for (int i = 0; i < 12; ++i) pd.error_limit[i] = derived_error[i];
    pd.error_limit_source = PulseLimitSource::kGlobal;
  }
}

// §30.7.3: SDF annotation of the pulse limits, which takes precedence over a
// PATHPULSE$ specparam and over the global invocation options alike, so this
// one writes whatever already stands.
void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error) {
  const uint64_t kEffectiveError = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = kEffectiveError;
  }
  pd.reject_limit_source = PulseLimitSource::kSdf;
  pd.error_limit_source = PulseLimitSource::kSdf;
}

namespace {

// Overwrites `existing` with `replacement`, holding back whichever pulse
// (reject/error) limits `retain` names at the values `existing` already had.
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

// Nonconditional update: overwrites every existing path delay between the same
// ports, but keeps each entry's original condition/ifnone (and whichever pulse
// limits are being held). Returns true if at least one entry matched.
//
// §30.3 puts a specify block inside a module declaration, so two instances of
// one cell declare paths carrying the same src_port and dst_port and are told
// apart only by PathDelay::inst_prefix. `match_inst_prefix` asks for that
// comparison: SpecifyManager::AddPathDelay sets it, so registering a second
// instance adds a path rather than overwriting the first instance's.
// SpecifyManager::AnnotateSdfPathDelay sets it too: SdfCellInstancePrefix
// (simulator/sdf_annotate.cpp) turns an SDF cell's instance path, below the
// §32.9 module_instance operand CellInScope filtered on, into the prefix
// stamped on the PathDelay, so one entry no longer reaches both in-scope
// instances of one cell.
bool UpdateNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                    const PathDelay& delay,
                                    PathDelayPulseRetention retain,
                                    bool match_inst_prefix) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
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

}  // namespace

void SpecifyManager::AddPathDelay(PathDelay delay, bool preserve_pulse_limits) {
  const PathDelayPulseRetention kRetain{preserve_pulse_limits,
                                        preserve_pulse_limits};
  const bool kSdfIsNonconditional = delay.condition.empty() && !delay.is_ifnone;
  if (kSdfIsNonconditional) {
    if (!UpdateNonconditionalPathDelays(path_delays_, delay, kRetain,
                                        /*match_inst_prefix=*/true)) {
      path_delays_.push_back(std::move(delay));
    }
    return;
  }
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.inst_prefix == delay.inst_prefix &&
        existing.condition == delay.condition &&
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
    if (!UpdateNonconditionalPathDelays(path_delays_, delay, retain,
                                        /*match_inst_prefix=*/true)) {
      path_delays_.push_back(std::move(delay));
    }
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
        existing.condition == delay.condition &&
        existing.is_ifnone == delay.is_ifnone) {
      ReplacePathDelayPreservingPulse(existing, std::move(delay), retain);
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
// `match_inst_prefix` means what it means in UpdateNonconditionalPathDelays
// above: with it set, PathDelay::inst_prefix is compared too, which is what
// tells the paths of one instance of a cell from those of another (§30.3).
bool IncrementNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                       const PathDelay& delta,
                                       bool match_inst_prefix) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port &&
        (!match_inst_prefix || existing.inst_prefix == delta.inst_prefix)) {
      AddPathDelayValues(existing, delta);
      matched = true;
    }
  }
  return matched;
}

// Adds `delta` to the first existing path delay matching ports plus
// condition/ifnone, and, when `match_inst_prefix` is set, the instance prefix
// as well. Returns true if a matching entry was found.
bool IncrementConditionalPathDelay(std::vector<PathDelay>& path_delays,
                                   const PathDelay& delta,
                                   bool match_inst_prefix) {
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port &&
        (!match_inst_prefix || existing.inst_prefix == delta.inst_prefix) &&
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
          ? IncrementNonconditionalPathDelays(path_delays_, delta,
                                              /*match_inst_prefix=*/false)
          : IncrementConditionalPathDelay(path_delays_, delta,
                                          /*match_inst_prefix=*/false);
  if (!kMatched) path_delays_.push_back(delta);
}

bool SpecifyManager::IncrementSdfPathDelay(const PathDelay& delta) {
  const bool kSdfIsNonconditional = delta.condition.empty() && !delta.is_ifnone;
  if (kSdfIsNonconditional) {
    // §32.9: the entry reaches the paths of the instance its cell named, which
    // AnnotateSdfIopathEntry (simulator/sdf_annotate.cpp) stamped onto
    // PathDelay::inst_prefix, so it is matched as AnnotateSdfPathDelay does.
    if (!IncrementNonconditionalPathDelays(path_delays_, delta,
                                           /*match_inst_prefix=*/true)) {
      path_delays_.push_back(delta);
    }
    return true;
  }
  // §32.4.1, as above: with no declared path carrying that condition there is
  // nothing to add to.
  return IncrementConditionalPathDelay(path_delays_, delta,
                                       /*match_inst_prefix=*/true);
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
}

}  // namespace

bool SpecifyManager::AnnotateSdfDeviceDelay(const SdfDeviceAnnotation& a) {
  // An entry with no operand is the whole-module row: it reaches every specify
  // path, because every specify path ends at a module output. An operand names
  // one output and narrows the entry to it; an operand that names no output
  // this manager knows about -- a submodule instance, whose own declarations
  // live with that submodule -- reaches nothing here.
  const bool kReachesAllOutputs = a.port_instance.empty();

  // SdfDeviceAnnotation carries no instance prefix, so both scans reach the
  // matching outputs of every in-scope instance rather than of the one instance
  // the entry's cell named, as AnnotateSdfDeviceEntry
  // (simulator/sdf_annotate.cpp) records. PrimitiveDriver
  // (simulator/specify_path_delay.h) has no inst_prefix field at all, so the
  // fallback scan could not tell them apart even were one carried.
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
  // to the primitives driving them instead. §32.8: a gate primitive is not a
  // specify path and carries three state transition delays rather than twelve,
  // so the entry's values reach it through the reduction rather than through
  // the twelve-slot expansion the paths above take.
  for (auto& driver : primitive_drivers_) {
    if (!kReachesAllOutputs && driver.output_port != a.port_instance) continue;
    ApplySdfDeviceThreeStateValues(driver, a);
    applied = true;
  }
  return applied;
}

void SpecifyManager::AnnotateSdf(SdfAnnotation annotation) {
  sdf_annotations_.push_back(std::move(annotation));
}

void SpecifyManager::AddPathDelayFromDecl(const SpecifyPathDecl& decl,
                                          SimContext& ctx, Arena& arena,
                                          bool default_pulse_limits,
                                          std::string_view inst_prefix) {
  PathDelay pd = BuildPathDelayFromDecl(decl, ctx, arena);
  // §30.4 names a path's terminals by the declaring module's own port names, so
  // the instance is what tells two instances of one cell apart.
  pd.inst_prefix = inst_prefix;
  if (default_pulse_limits) InitDefaultPulseLimits(pd);
  AddPathDelay(std::move(pd));
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

}  // namespace delta
