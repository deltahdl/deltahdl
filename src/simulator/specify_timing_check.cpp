#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/variable.h"

namespace delta {

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

namespace {

// §32.4.4: SDF writes a hierarchical name with `/` between levels, while the
// design writes it with `.`. Neither spelling is preferred -- a name is kept as
// whoever wrote it spelled it -- so the two dividers compare equal instead.
bool IsInterconnectDivider(char c) { return c == '/' || c == '.'; }

bool InterconnectNameEq(std::string_view a, std::string_view b) {
  if (a.size() != b.size()) return false;
  for (std::size_t i = 0; i < a.size(); ++i) {
    if (a[i] == b[i]) continue;
    if (IsInterconnectDivider(a[i]) && IsInterconnectDivider(b[i])) continue;
    return false;
  }
  return true;
}

std::string JoinInterconnectScope(const std::string& scope,
                                  std::string_view leaf) {
  if (leaf.empty()) return scope;
  if (scope.empty()) return std::string(leaf);
  return scope + "/" + std::string(leaf);
}

// The enclosing scope of a hierarchical name -- "u2" for "u2/in", empty for a
// name at the top level.
std::string InterconnectScopeOf(const std::string& name) {
  for (std::size_t i = name.size(); i > 0; --i) {
    if (IsInterconnectDivider(name[i - 1])) return name.substr(0, i - 1);
  }
  return {};
}

// How deep in the hierarchy a name sits. A larger number is further from the
// top, which is what "hierarchically below" means for the up- and
// down-hierarchy annotation rules.
std::size_t InterconnectDepth(const std::string& name) {
  std::size_t depth = 0;
  for (char c : name) {
    if (IsInterconnectDivider(c)) ++depth;
  }
  return depth;
}

bool IsWithinInterconnectScope(std::string_view name, std::string_view scope) {
  if (scope.empty()) return true;
  if (InterconnectNameEq(name, scope)) return true;
  return name.size() > scope.size() &&
         InterconnectNameEq(name.substr(0, scope.size()), scope) &&
         IsInterconnectDivider(name[scope.size()]);
}

// §32.4.4: a load port shall be an input or an inout port, and a source port
// shall be an output or an inout port.
bool IsInterconnectLoadDirection(Direction dir) {
  return dir == Direction::kInput || dir == Direction::kInout;
}

bool IsInterconnectSourceDirection(Direction dir) {
  return dir == Direction::kOutput || dir == Direction::kInout;
}

const InterconnectTerminal* FindInterconnectTerminal(
    const InterconnectTopology& topo, std::string_view name) {
  for (const auto& t : topo.terminals) {
    if (InterconnectNameEq(t.name, name)) return &t;
  }
  return nullptr;
}

const InterconnectNet* FindInterconnectNet(const InterconnectTopology& topo,
                                           std::string_view name) {
  for (const auto& n : topo.nets) {
    if (InterconnectNameEq(n.name, name)) return &n;
  }
  return nullptr;
}

// §32.4.4: interconnect delays go between module ports and never between
// primitive pins, so a name that reaches into a gate instantiation is refused.
bool NamesInterconnectPrimitivePin(const InterconnectTopology& topo,
                                   std::string_view name) {
  for (const auto& inst : topo.primitive_instances) {
    if (IsWithinInterconnectScope(name, inst)) return true;
  }
  return false;
}

std::vector<const InterconnectTerminal*> InterconnectLoadsOnNet(
    const InterconnectTopology& topo, const std::string& net_id) {
  std::vector<const InterconnectTerminal*> out;
  for (const auto& t : topo.terminals) {
    if (t.is_primitive_pin || t.net != net_id) continue;
    if (IsInterconnectLoadDirection(t.direction)) out.push_back(&t);
  }
  return out;
}

std::vector<const InterconnectTerminal*> InterconnectSourcesOnNet(
    const InterconnectTopology& topo, const std::string& net_id) {
  std::vector<const InterconnectTerminal*> out;
  for (const auto& t : topo.terminals) {
    if (t.is_primitive_pin || t.net != net_id) continue;
    if (IsInterconnectSourceDirection(t.direction)) out.push_back(&t);
  }
  return out;
}

// §32.4.4: the load ports one entry's load name stands for. A name that is a
// port is just that port. A name that is a net stands for every load port of
// that net at or hierarchically within the net's own scope, and any other name
// stands for every load port hierarchically within it -- which is how two
// annotations onto the same net can cover different, overlapping subsets of its
// ports.
// A name that is a port is just that port, plus the ports of the net at or
// hierarchically within that point -- the ports inside the instance whose port
// was named.
static std::vector<const InterconnectTerminal*> LoadsUnderPort(
    const InterconnectTopology& topo, const InterconnectTerminal* exact) {
  std::vector<const InterconnectTerminal*> out;
  out.push_back(exact);
  const std::string kScope = InterconnectScopeOf(exact->name);
  const std::size_t kDepth = InterconnectDepth(exact->name);
  for (const auto* load : InterconnectLoadsOnNet(topo, exact->net)) {
    if (load == exact) continue;
    if (InterconnectDepth(load->name) <= kDepth) continue;
    if (!IsWithinInterconnectScope(load->name, kScope)) continue;
    out.push_back(load);
  }
  return out;
}

// A name that is a net stands for every load port of that net at or
// hierarchically within the net's own scope.
static std::vector<const InterconnectTerminal*> LoadsOnNamedNet(
    const InterconnectTopology& topo, const InterconnectNet* net) {
  const std::string kScope = InterconnectScopeOf(net->name);
  std::vector<const InterconnectTerminal*> out;
  for (const auto* load : InterconnectLoadsOnNet(topo, net->id)) {
    if (IsWithinInterconnectScope(load->name, kScope)) out.push_back(load);
  }
  return out;
}

// Any other name stands for every load port hierarchically within it.
static std::vector<const InterconnectTerminal*> LoadsWithinScope(
    const InterconnectTopology& topo, std::string_view name) {
  std::vector<const InterconnectTerminal*> out;
  for (const auto& t : topo.terminals) {
    if (t.is_primitive_pin || !IsInterconnectLoadDirection(t.direction)) {
      continue;
    }
    if (t.name.size() > name.size() &&
        InterconnectNameEq(std::string_view(t.name).substr(0, name.size()),
                           name) &&
        IsInterconnectDivider(t.name[name.size()])) {
      out.push_back(&t);
    }
  }
  return out;
}

std::vector<const InterconnectTerminal*> ResolveInterconnectLoads(
    const InterconnectTopology& topo, std::string_view name) {
  if (const auto* exact = FindInterconnectTerminal(topo, name);
      exact != nullptr) {
    return LoadsUnderPort(topo, exact);
  }
  if (const auto* net = FindInterconnectNet(topo, name); net != nullptr) {
    return LoadsOnNamedNet(topo, net);
  }
  return LoadsWithinScope(topo, name);
}

// Which of the twelve transition slots a value change of a one-bit signal took.
// Only the six two-state transitions are distinguished here; a change into or
// out of x or z lands on the matching slot of Table 30-3's ordering.
uint8_t InterconnectTransitionSlot(uint64_t from, uint64_t to) {
  const bool kFromZero = from == 0;
  const bool kToZero = to == 0;
  if (kFromZero && !kToZero) return 0;  // 0 -> 1
  if (!kFromZero && kToZero) return 1;  // 1 -> 0
  return 0;
}

// §32.5: whether some entry naming its own source already carries the delay
// from `source` to `load` -- which is exactly what an INTERCONNECT annotation
// written after a PORT annotation to the same load leaves standing beside the
// PORT's all-sources entry.
bool InterconnectSourceClaimed(const std::vector<InterconnectDelay>& delays,
                               std::string_view load, std::string_view source) {
  for (const auto& delay : delays) {
    if (delay.covered_sources.empty()) continue;
    if (!InterconnectNameEq(delay.dst_port, load)) continue;
    for (const auto& covered : delay.covered_sources) {
      if (InterconnectNameEq(covered, source)) return true;
    }
  }
  return false;
}

// §32.4.4: the design-side name whose value an annotated load follows. A delay
// from one named source follows that source; a delay standing for all sources
// on the net follows whichever source drives the load's net.
//
// §32.5: a source a later INTERCONNECT annotation named is not one of those,
// though. Only the delay from that source was meant to change, so the source
// keeps to its own entry and the all-sources entry moves on to a source no
// entry of its own covers.
std::string InterconnectSourceStorageName(
    const InterconnectTopology& topo,
    const std::vector<InterconnectDelay>& all_delays,
    const InterconnectDelay& delay) {
  std::string source;
  if (!delay.covered_sources.empty()) {
    source = delay.covered_sources.front();
  } else if (const auto* load = FindInterconnectTerminal(topo, delay.dst_port);
             load != nullptr) {
    for (const auto* candidate : InterconnectSourcesOnNet(topo, load->net)) {
      if (InterconnectSourceClaimed(all_delays, delay.dst_port,
                                    candidate->name)) {
        continue;
      }
      source = candidate->name;
      break;
    }
  }
  if (source.empty()) return {};
  for (char& c : source) {
    if (c == '/') c = '.';
  }
  return source;
}

// The module a hierarchical instantiation names, or null when the compilation
// unit declares no such module.
const ModuleDecl* FindInterconnectModule(const CompilationUnit& cu,
                                         std::string_view name) {
  for (const auto* mod : cu.modules) {
    if (mod != nullptr && mod->name == name) return mod;
  }
  return nullptr;
}

// §32.4.4: builds the topology. Nets that a port connection joins are merged
// into one identity, so the ports on either side of a hierarchy boundary come
// out on the same net -- which is what lets an annotation to a port reach the
// connected ports at higher and lower levels.
class InterconnectTopologyBuilder {
 public:
  explicit InterconnectTopologyBuilder(const CompilationUnit& cu) : cu_(cu) {}

  InterconnectTopology Build(const ModuleDecl& top) {
    Walk(top, "", 0);
    for (auto& t : topo_.terminals) t.net = Find(t.net);
    for (auto& n : topo_.nets) n.id = Find(n.id);
    return std::move(topo_);
  }

 private:
  std::string Find(const std::string& net) {
    auto it = parent_.find(net);
    if (it == parent_.end()) return net;
    if (it->second == net) return net;
    std::string root = Find(it->second);
    it->second = root;
    return root;
  }

  void Union(const std::string& a, const std::string& b) {
    const std::string kRootA = Find(a);
    const std::string kRootB = Find(b);
    if (kRootA == kRootB) return;
    parent_[kRootB] = kRootA;
  }

  void AddNet(const std::string& name) {
    parent_.emplace(name, name);
    for (const auto& n : topo_.nets) {
      if (n.name == name) return;
    }
    topo_.nets.push_back({name, name});
  }

  void WalkItem(const ModuleItem& item, const std::string& scope, int depth) {
    if (item.kind == ModuleItemKind::kNetDecl ||
        item.kind == ModuleItemKind::kVarDecl) {
      if (!item.name.empty()) AddNet(JoinInterconnectScope(scope, item.name));
      return;
    }
    if (item.kind == ModuleItemKind::kGateInst) {
      if (!item.gate_inst_name.empty()) {
        topo_.primitive_instances.push_back(
            JoinInterconnectScope(scope, item.gate_inst_name));
      }
      return;
    }
    if (item.kind == ModuleItemKind::kModuleInst)
      WalkInstance(item, scope, depth);
  }

  void Walk(const ModuleDecl& mod, const std::string& scope, int depth) {
    if (depth > 16) return;  // a self-instantiating module cannot be elaborated
    for (const auto& port : mod.ports) {
      if (!port.name.empty()) AddNet(JoinInterconnectScope(scope, port.name));
    }
    for (const auto* item : mod.items) {
      if (item != nullptr) WalkItem(*item, scope, depth);
    }
  }

  // §23.3.2.1: a connection with no formal name is positional, so the port it
  // reaches is the one declared in that position.
  void AddInstancePortTerminal(const ModuleItem& item, const ModuleDecl& child,
                               std::size_t i, const std::string& scope,
                               const std::string& inst) {
    const auto& [formal, actual] = item.inst_ports[i];
    std::string_view port_name = formal;
    Direction dir = Direction::kNone;
    if (port_name.empty()) {
      if (i >= child.ports.size()) return;
      port_name = child.ports[i].name;
      dir = child.ports[i].direction;
    } else {
      for (const auto& p : child.ports) {
        if (p.name == port_name) dir = p.direction;
      }
    }
    if (port_name.empty()) return;

    InterconnectTerminal terminal;
    terminal.name = JoinInterconnectScope(inst, port_name);
    terminal.direction = dir;
    terminal.net = terminal.name;
    AddNet(terminal.name);
    if (actual != nullptr && actual->kind == ExprKind::kIdentifier &&
        !actual->text.empty()) {
      const std::string kOuter = JoinInterconnectScope(scope, actual->text);
      AddNet(kOuter);
      Union(kOuter, terminal.name);
    }
    topo_.terminals.push_back(std::move(terminal));
  }

  void WalkInstance(const ModuleItem& item, const std::string& scope,
                    int depth) {
    const ModuleDecl* child = FindInterconnectModule(cu_, item.inst_module);
    if (child == nullptr) return;
    const std::string kInst = JoinInterconnectScope(scope, item.inst_name);

    for (std::size_t i = 0; i < item.inst_ports.size(); ++i) {
      AddInstancePortTerminal(item, *child, i, scope, kInst);
    }
    Walk(*child, kInst, depth + 1);
  }

  const CompilationUnit& cu_;
  InterconnectTopology topo_;
  std::unordered_map<std::string, std::string> parent_;
};

}  // namespace

InterconnectTopology CollectInterconnectTopology(const CompilationUnit& cu,
                                                 const ModuleDecl& top) {
  return InterconnectTopologyBuilder(cu).Build(top);
}

void SpecifyManager::BindDesignInterconnect(InterconnectTopology topology) {
  topology_ = std::move(topology);
}

void SpecifyManager::PlaceInterconnectDelay(
    const SdfInterconnectAnnotation& annotation, const std::string& source,
    const std::string& load, std::vector<std::string> covered_sources) {
  InterconnectDelay delay;
  delay.src_port = source;
  delay.dst_port = load;
  delay.rise = annotation.delays[0];
  delay.fall = annotation.delays[1];
  for (int i = 0; i < 12; ++i) delay.delays[i] = annotation.delays[i];
  // §32.4.4: an interconnect delay carries its own reject and error pulse limit
  // for each of the twelve transitions, and it gets them by the rule a specify
  // path delay's limits follow -- each limit derived from that transition's own
  // delay under whatever pulse-limit percentages are in effect.
  DerivePulseLimitsFromDelays(delay.delays, reject_pulse_pct_, error_pulse_pct_,
                              delay.reject_limit, delay.error_limit);
  delay.covered_sources = std::move(covered_sources);
  if (annotation.is_increment) {
    IncrementInterconnectDelay(delay);
    return;
  }
  AddInterconnectDelay(std::move(delay));
}

// §32.4.4: a PORT entry names the load port directly and carries no source, so
// its delay is the delay from every source on the net to that port.
SdfInterconnectOutcome SpecifyManager::AnnotateSdfPortDelay(
    const SdfInterconnectAnnotation& annotation, const std::string& load_name) {
  SdfInterconnectOutcome out;
  const auto* port = FindInterconnectTerminal(topology_, load_name);
  if (port == nullptr) {
    out.warnings.push_back("SDF annotator: unable to annotate PORT delay on " +
                           load_name + ", which names no port");
    return out;
  }
  if (!IsInterconnectLoadDirection(port->direction)) {
    out.warnings.push_back("SDF annotator: unable to annotate PORT delay on " +
                           load_name + ", which is not an input or inout port");
    return out;
  }
  PlaceInterconnectDelay(annotation, {}, port->name, {});
  out.annotated = true;
  return out;
}

// §32.4.4: a NETDELAY entry names either a port or a net, and the annotator has
// to work out which before it can decide what to annotate. Annotating to a net
// reaches every load port connected to it.
SdfInterconnectOutcome SpecifyManager::AnnotateSdfNetDelay(
    const SdfInterconnectAnnotation& annotation, const std::string& load_name) {
  SdfInterconnectOutcome out;
  if (const auto* port = FindInterconnectTerminal(topology_, load_name);
      port != nullptr) {
    if (!IsInterconnectLoadDirection(port->direction)) {
      out.warnings.push_back(
          "SDF annotator: unable to annotate NETDELAY delay on " + load_name +
          ", which is not an input or inout module port or a net");
      return out;
    }
    PlaceInterconnectDelay(annotation, {}, port->name, {});
    out.annotated = true;
    return out;
  }
  const auto* net = FindInterconnectNet(topology_, load_name);
  if (net == nullptr) {
    out.warnings.push_back(
        "SDF annotator: unable to annotate NETDELAY delay on " + load_name +
        ", which names neither a port nor a net");
    return out;
  }
  const auto kLoads = InterconnectLoadsOnNet(topology_, net->id);
  if (kLoads.empty()) {
    out.warnings.push_back(
        "SDF annotator: unable to annotate NETDELAY delay on net " + load_name +
        ", which has no load ports");
    return out;
  }
  for (const auto* load : kLoads) {
    PlaceInterconnectDelay(annotation, {}, load->name, {});
  }
  out.annotated = true;
  return out;
}

// §32.4.4: a load port shall be an input or inout port; one that is not is
// dropped from the set the annotation reaches, with a warning.
std::vector<const InterconnectTerminal*>
SpecifyManager::ResolveInterconnectLoadPorts(const std::string& load_name,
                                             SdfInterconnectOutcome& out) {
  std::vector<const InterconnectTerminal*> loads =
      ResolveInterconnectLoads(topology_, load_name);
  const std::size_t kBefore = loads.size();
  loads.erase(
      std::remove_if(loads.begin(), loads.end(),
                     [](const InterconnectTerminal* t) {
                       return !IsInterconnectLoadDirection(t->direction);
                     }),
      loads.end());
  if (loads.size() != kBefore) {
    out.warnings.push_back("SDF annotator: INTERCONNECT load " + load_name +
                           " is not an input or inout port");
  }
  if (loads.empty() && kBefore == 0) {
    out.warnings.push_back(
        "SDF annotator: unable to annotate INTERCONNECT delay on " + load_name +
        ", which names no load port");
  }
  return loads;
}

// §32.4.4: a source port shall be an output or inout port; one that is not
// cannot be the source of this delay.
const InterconnectTerminal* SpecifyManager::ResolveInterconnectSourcePort(
    const std::string& source_name, SdfInterconnectOutcome& out) const {
  const InterconnectTerminal* source =
      source_name.empty() ? nullptr
                          : FindInterconnectTerminal(topology_, source_name);
  if (source != nullptr && !IsInterconnectSourceDirection(source->direction)) {
    out.warnings.push_back("SDF annotator: INTERCONNECT source " + source_name +
                           " is not an output or inout port");
    return nullptr;
  }
  return source;
}

// §32.4.4: a delay from a source that sits higher in the hierarchy than the
// load is a delay from every source at or above that source port.
std::vector<std::string> SpecifyManager::CoveredSourcesOnSameNet(
    const InterconnectTerminal* source,
    const InterconnectTerminal* first_load) const {
  std::vector<std::string> covered{source->name};
  if (InterconnectDepth(source->name) >= InterconnectDepth(first_load->name))
    return covered;
  for (const auto* other : InterconnectSourcesOnNet(topology_, source->net)) {
    if (other->name == source->name) continue;
    if (InterconnectDepth(other->name) <= InterconnectDepth(source->name)) {
      covered.push_back(other->name);
    }
  }
  return covered;
}

// §32.4.4: a source that is not found, or that is not on the load's net, is
// warned about, but the delay still reaches the load. On a multisource net it
// is then taken as the delay from all sources, exactly as a PORT delay is;
// elsewhere it stays the delay from the source the entry named.
std::vector<std::string> SpecifyManager::CoveredSourcesOffNet(
    const InterconnectTerminal* source, const std::string& source_name,
    const std::string& load_name, const InterconnectTerminal* first_load,
    SdfInterconnectOutcome& out) const {
  const std::string kNamed =
      source_name.empty() ? std::string("(none)") : source_name;
  const std::string kReason =
      source == nullptr ? kNamed + " not found"
                        : kNamed + " is not on the same net as " + load_name;
  out.warnings.push_back("SDF annotator: INTERCONNECT source " + kReason +
                         "; delay annotated to " + load_name + " anyway");
  std::vector<std::string> covered;
  const bool kMultisource =
      InterconnectSourcesOnNet(topology_, first_load->net).size() > 1;
  if (!kMultisource && !source_name.empty()) covered.push_back(source_name);
  return covered;
}

// §32.4.4: an up-hierarchy annotation, where the load sits above the source,
// gives every load port above that load the same delay as the load itself.
void SpecifyManager::ExtendLoadsUpHierarchy(
    const InterconnectTerminal* source,
    std::vector<const InterconnectTerminal*>& loads) const {
  const std::size_t kLoadDepth = InterconnectDepth(loads.front()->name);
  if (kLoadDepth >= InterconnectDepth(source->name)) return;
  for (const auto* other : InterconnectLoadsOnNet(topology_, source->net)) {
    if (InterconnectDepth(other->name) >= kLoadDepth) continue;
    if (std::find(loads.begin(), loads.end(), other) != loads.end()) continue;
    loads.push_back(other);
  }
}

// §32.4.4: an INTERCONNECT entry names a source and a load, and the delay is
// annotated onto every load port the load name reaches.
SdfInterconnectOutcome SpecifyManager::AnnotateSdfInterconnectPath(
    const SdfInterconnectAnnotation& annotation, const std::string& load_name,
    const std::string& source_name) {
  SdfInterconnectOutcome out;
  std::vector<const InterconnectTerminal*> loads =
      ResolveInterconnectLoadPorts(load_name, out);
  if (loads.empty()) return out;

  const InterconnectTerminal* source =
      ResolveInterconnectSourcePort(source_name, out);
  const bool kSameNet =
      source != nullptr && std::any_of(loads.begin(), loads.end(),
                                       [&](const InterconnectTerminal* t) {
                                         return t->net == source->net;
                                       });

  std::vector<std::string> covered;
  if (kSameNet) {
    covered = CoveredSourcesOnSameNet(source, loads.front());
    ExtendLoadsUpHierarchy(source, loads);
  } else {
    covered = CoveredSourcesOffNet(source, source_name, load_name,
                                   loads.front(), out);
  }

  for (const auto* load : loads) {
    PlaceInterconnectDelay(annotation,
                           covered.empty() ? std::string() : covered.front(),
                           load->name, covered);
  }
  out.annotated = true;
  return out;
}

SdfInterconnectOutcome SpecifyManager::AnnotateSdfInterconnect(
    const SdfInterconnectAnnotation& annotation) {
  SdfInterconnectOutcome out;
  // The names stay exactly as the file spelled them; only comparison is
  // divider-insensitive, so nothing an entry carries is rewritten.
  const std::string& load_name = annotation.load;
  const std::string& source_name = annotation.source;

  // With no design bound there is nothing to look the entry's names up in, so
  // the entry is taken as written.
  if (topology_.terminals.empty() && topology_.nets.empty()) {
    std::vector<std::string> covered;
    if (!source_name.empty()) covered.push_back(source_name);
    PlaceInterconnectDelay(annotation, source_name, load_name,
                           std::move(covered));
    out.annotated = true;
    return out;
  }

  // §32.4.4: an interconnect delay is annotated between module ports, never
  // between primitive pins.
  if (NamesInterconnectPrimitivePin(topology_, load_name) ||
      (!source_name.empty() &&
       NamesInterconnectPrimitivePin(topology_, source_name))) {
    out.warnings.push_back(
        "SDF annotator: interconnect delay names a primitive pin (" +
        (source_name.empty() ? load_name : source_name + " -> " + load_name) +
        "), which is not a module port");
    return out;
  }

  if (annotation.construct == SdfInterconnectConstruct::kPort)
    return AnnotateSdfPortDelay(annotation, load_name);
  if (annotation.construct == SdfInterconnectConstruct::kNetdelay)
    return AnnotateSdfNetDelay(annotation, load_name);
  return AnnotateSdfInterconnectPath(annotation, load_name, source_name);
}

const InterconnectDelay* SpecifyManager::FindInterconnectDelay(
    std::string_view source, std::string_view load) const {
  // §32.5: a PORT annotation followed by an INTERCONNECT annotation to the same
  // load leaves both entries standing, and only the delay from the source the
  // INTERCONNECT named is meant to have changed. So an entry that names this
  // very source is what the source reads, and the all-sources entry the PORT
  // left behind is what every other source keeps reading. Only these two can
  // coexist: a PORT written afterwards discards the source-specific entries on
  // its load, so preferring the named source is also preferring the later
  // annotation.
  const InterconnectDelay* all_sources = nullptr;
  for (const auto& delay : interconnect_delays_) {
    if (!InterconnectNameEq(delay.dst_port, load)) continue;
    // A delay recorded with no source is the delay from all sources, so it is
    // the delay from whichever source is being asked about.
    if (delay.covered_sources.empty()) {
      if (all_sources == nullptr) all_sources = &delay;
      continue;
    }
    for (const auto& covered : delay.covered_sources) {
      if (InterconnectNameEq(covered, source)) return &delay;
    }
  }
  return all_sources;
}

// The net a name sits on, whether it names a terminal or the net itself. Empty
// when the name is on no net the topology knows.
std::string SpecifyManager::InterconnectNetIdOf(std::string_view name) const {
  if (const auto* terminal = FindInterconnectTerminal(topology_, name))
    return terminal->net;
  if (const auto* net = FindInterconnectNet(topology_, name)) return net->id;
  return {};
}

// Whether one annotated delay's load is the load `name` reads through: the load
// sits on the same net, and `name` is hierarchically within the load's scope.
bool SpecifyManager::DelayLoadCoversReference(const InterconnectDelay& delay,
                                              const std::string& net_id,
                                              std::string_view name) const {
  const auto* load = FindInterconnectTerminal(topology_, delay.dst_port);
  if (load == nullptr || load->net != net_id) return false;
  const std::string kLoadScope = InterconnectScopeOf(load->name);
  return !kLoadScope.empty() && IsWithinInterconnectScope(name, kLoadScope);
}

InterconnectReferenceRead SpecifyManager::ReadInterconnectReference(
    std::string_view name) const {
  for (const auto& delay : interconnect_delays_) {
    if (InterconnectNameEq(delay.dst_port, name)) {
      return {true, delay.delays[0], delay.dst_port};
    }
  }
  // §32.4.4: a reference hierarchically after the load reads the delayed value
  // too, which is any reference inside the instance whose port is the load and
  // that still names the same net.
  const std::string kNetId = InterconnectNetIdOf(name);
  if (!kNetId.empty()) {
    for (const auto& delay : interconnect_delays_) {
      if (!DelayLoadCoversReference(delay, kNetId, name)) continue;
      return {true, delay.delays[0], delay.dst_port};
    }
  }
  // §32.4.4: everything else -- the source itself, and every point on the net
  // before the load -- reads the undelayed value.
  return {};
}

void SpecifyManager::StartInterconnectPropagation(SimContext& ctx,
                                                  Scheduler& scheduler) {
  interconnect_ctx_ = &ctx;
  interconnect_scheduler_ = &scheduler;
  interconnect_last_source_value_.clear();
  interconnect_arrivals_.clear();
  // Take the values standing now as the starting point, so only transitions
  // from here on produce an arrival at a load.
  PollInterconnectSources();
  scheduler.SetPostTimestepCallback([this]() { PollInterconnectSources(); });
}

void SpecifyManager::PollInterconnectSources() {
  if (interconnect_ctx_ == nullptr || interconnect_scheduler_ == nullptr) {
    return;
  }
  for (const auto& delay : interconnect_delays_) {
    const std::string kStorage =
        InterconnectSourceStorageName(topology_, interconnect_delays_, delay);
    if (kStorage.empty()) continue;
    Variable* var = interconnect_ctx_->FindVariable(kStorage);
    if (var == nullptr) continue;
    const uint64_t kValue = var->value.ToUint64();
    // §32.5: one load can carry two entries at once -- the all-sources delay a
    // PORT annotation left and the delay from the one source a later
    // INTERCONNECT annotation named -- so each is watched against the source it
    // follows rather than against the load they share.
    const std::string kWatched = kStorage + "->" + delay.dst_port;
    auto it = interconnect_last_source_value_.find(kWatched);
    if (it == interconnect_last_source_value_.end()) {
      interconnect_last_source_value_.emplace(kWatched, kValue);
      continue;
    }
    if (it->second == kValue) continue;
    const uint8_t kSlot = InterconnectTransitionSlot(it->second, kValue);
    it->second = kValue;
    const uint64_t kDelay = delay.delays[kSlot];
    const uint64_t kNow = interconnect_scheduler_->CurrentTime().ticks;
    InterconnectArrival arrival;
    arrival.load_port = delay.dst_port;
    arrival.value = kValue;
    arrival.time = kNow + kDelay;
    arrival.delay = kDelay;
    if (kDelay == 0) {
      // The current time slot is already being torn down, so a zero delay
      // arrives right here rather than through the event queue.
      interconnect_arrivals_.push_back(std::move(arrival));
      continue;
    }
    Event* event = interconnect_scheduler_->GetEventPool().Acquire();
    event->kind = EventKind::kEvaluation;
    event->callback = [this, arrival]() {
      interconnect_arrivals_.push_back(arrival);
    };
    interconnect_scheduler_->ScheduleEvent(SimTime{kNow + kDelay},
                                           Region::kActive, event);
  }
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
