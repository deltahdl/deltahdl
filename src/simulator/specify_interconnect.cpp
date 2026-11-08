#include <algorithm>
#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_sdf.h"

namespace delta {

namespace {

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

std::string InterconnectScopeOf(const std::string& name) {
  for (std::size_t i = name.size(); i > 0; --i) {
    if (IsInterconnectDivider(name[i - 1])) return name.substr(0, i - 1);
  }
  return {};
}

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

static std::vector<const InterconnectTerminal*> LoadsOnNamedNet(
    const InterconnectTopology& topo, const InterconnectNet* net) {
  const std::string kScope = InterconnectScopeOf(net->name);
  std::vector<const InterconnectTerminal*> out;
  for (const auto* load : InterconnectLoadsOnNet(topo, net->id)) {
    if (IsWithinInterconnectScope(load->name, kScope)) out.push_back(load);
  }
  return out;
}

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

const ModuleDecl* FindInterconnectModule(const CompilationUnit& cu,
                                         std::string_view name) {
  for (const auto* mod : cu.modules) {
    if (mod != nullptr && mod->name == name) return mod;
  }
  return nullptr;
}

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
    if (item.kind == ModuleItemKind::kGateInst ||
        item.kind == ModuleItemKind::kUdpInst) {
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
    if (depth > 16) return;
    for (const auto& port : mod.ports) {
      if (!port.name.empty()) AddNet(JoinInterconnectScope(scope, port.name));
    }
    for (const auto* item : mod.items) {
      if (item != nullptr) WalkItem(*item, scope, depth);
    }
  }

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
    const std::string kInst = JoinInterconnectScope(scope, item.inst_name);
    if (child == nullptr) {
      const bool kIsUdp = std::ranges::any_of(
          cu_.udps,
          [&](const UdpDecl* udp) { return udp->name == item.inst_module; });
      if (kIsUdp) topo_.primitive_instances.push_back(kInst);
      return;
    }

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

const InterconnectDelay* SpecifyManager::PriorInterconnectDelay(
    const std::string& source, const std::string& load) const {
  const InterconnectDelay* all_sources = nullptr;
  for (const auto& delay : interconnect_delays_) {
    if (delay.dst_port != load) continue;
    if (!source.empty() && delay.src_port == source) return &delay;
    if (delay.covered_sources.empty()) all_sources = &delay;
  }
  return all_sources;
}

namespace {

void HoldInterconnectDelays(InterconnectDelay& delay,
                            const SdfInterconnectAnnotation& annotation,
                            const InterconnectDelay* prior) {
  for (std::size_t i = 0; i < 12; ++i) {
    delay.delays[i] = annotation.delays[i];
    if (!annotation.held.delay[i]) continue;
    delay.delays[i] =
        annotation.is_increment || prior == nullptr ? 0 : prior->delays[i];
  }
}

void PlaceStatedInterconnectLimits(InterconnectDelay& delay,
                                   const SdfInterconnectAnnotation& annotation,
                                   const InterconnectDelay* prior) {
  for (std::size_t i = 0; i < 12; ++i) {
    const bool kHoldReject = annotation.limits_written
                                 ? annotation.held.reject[i]
                                 : annotation.held.delay[i];
    const bool kHoldError = annotation.limits_written
                                ? annotation.held.error[i]
                                : annotation.held.delay[i];
    if (annotation.limits_written && !kHoldReject) {
      delay.reject_limit[i] = annotation.reject_limit[i];
    } else if (kHoldReject && prior != nullptr) {
      delay.reject_limit[i] = prior->reject_limit[i];
    }
    if (annotation.limits_written && !kHoldError) {
      delay.error_limit[i] = annotation.error_limit[i];
    } else if (kHoldError && prior != nullptr) {
      delay.error_limit[i] = prior->error_limit[i];
    }
  }
}

}  // namespace

void SpecifyManager::PlaceInterconnectDelay(
    const SdfInterconnectAnnotation& annotation, const std::string& source,
    const std::string& load, std::vector<std::string> covered_sources) {
  InterconnectDelay delay;
  delay.src_port = source;
  delay.dst_port = load;
  const InterconnectDelay* prior = PriorInterconnectDelay(source, load);
  HoldInterconnectDelays(delay, annotation, prior);
  delay.rise = delay.delays[0];
  delay.fall = delay.delays[1];
  delay.covered_sources = std::move(covered_sources);
  if (annotation.is_increment) {
    for (std::size_t i = 0; i < 12; ++i) {
      delay.reject_limit[i] =
          annotation.held.reject[i] ? 0 : annotation.reject_limit[i];
      delay.error_limit[i] =
          annotation.held.error[i] ? 0 : annotation.error_limit[i];
    }
    IncrementInterconnectDelay(delay);
    return;
  }
  DerivePulseLimitsFromDelays(delay.delays, reject_pulse_pct_, error_pulse_pct_,
                              delay.reject_limit, delay.error_limit);
  PlaceStatedInterconnectLimits(delay, annotation, prior);
  AddInterconnectDelay(std::move(delay));
}

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

static bool InterconnectScopeWithin(std::string_view inner,
                                    std::string_view outer) {
  if (outer.empty()) return true;
  return inner.size() > outer.size() &&
         InterconnectNameEq(inner.substr(0, outer.size()), outer) &&
         IsInterconnectDivider(inner[outer.size()]);
}

std::vector<std::string> SpecifyManager::CoveredSourcesOnSameNet(
    const InterconnectTerminal* source) const {
  std::vector<std::string> covered{source->name};
  const std::string kScope = InterconnectScopeOf(source->name);
  for (const auto* other : InterconnectSourcesOnNet(topology_, source->net)) {
    if (other->name == source->name) continue;
    const std::string kOther = InterconnectScopeOf(other->name);
    if (InterconnectScopeWithin(kScope, kOther) ||
        InterconnectScopeWithin(kOther, kScope)) {
      covered.push_back(other->name);
    }
  }
  return covered;
}

std::vector<std::string> SpecifyManager::CoveredSourcesOffNet(
    const InterconnectTerminal* source, const std::string& source_name,
    const std::string& load_name, SdfInterconnectOutcome& out) const {
  const std::string kNamed =
      source_name.empty() ? std::string("(none)") : source_name;
  const std::string kReason =
      source == nullptr ? kNamed + " not found"
                        : kNamed + " is not on the same net as " + load_name;
  out.warnings.push_back("SDF annotator: INTERCONNECT source " + kReason +
                         "; delay annotated to " + load_name + " anyway");
  return {};
}

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
    covered = CoveredSourcesOnSameNet(source);
    ExtendLoadsUpHierarchy(source, loads);
  } else {
    covered = CoveredSourcesOffNet(source, source_name, load_name, out);
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
  const std::string& load_name = annotation.load;
  const std::string& source_name = annotation.source;

  if (topology_.terminals.empty() && topology_.nets.empty()) {
    std::vector<std::string> covered;
    if (!source_name.empty()) covered.push_back(source_name);
    PlaceInterconnectDelay(annotation, source_name, load_name,
                           std::move(covered));
    out.annotated = true;
    return out;
  }

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
  const InterconnectDelay* all_sources = nullptr;
  const InterconnectDelay* same_net = nullptr;
  const std::string kSourceNet = AskedSourceNet(source);
  for (const auto& delay : interconnect_delays_) {
    if (!InterconnectNameEq(delay.dst_port, load)) continue;
    if (delay.covered_sources.empty()) {
      if (all_sources == nullptr) all_sources = &delay;
      continue;
    }
    const SourceMatch kMatch = CoveredSourceMatch(delay, source, kSourceNet);
    if (kMatch == SourceMatch::kNamed) return &delay;
    if (kMatch == SourceMatch::kSameNet && same_net == nullptr)
      same_net = &delay;
  }
  return same_net != nullptr ? same_net : all_sources;
}

bool SpecifyManager::HasSourceSpecificInterconnectDelay(
    std::string_view load) const {
  return std::ranges::any_of(interconnect_delays_,
                             [load](const InterconnectDelay& delay) {
                               return !delay.covered_sources.empty() &&
                                      InterconnectNameEq(delay.dst_port, load);
                             });
}

std::optional<InterconnectDelay> SpecifyManager::ConnectionInterconnectDelay(
    std::string_view source, std::string_view load) const {
  const InterconnectDelay* at_load = FindInterconnectDelay(source, load);
  if (at_load == nullptr) return std::nullopt;
  InterconnectDelay remaining = *at_load;
  const InterconnectTerminal* via = FindInterconnectTerminal(topology_, source);
  if (via == nullptr || !IsInterconnectLoadDirection(via->direction)) {
    return remaining;
  }
  for (const auto& upstream : interconnect_delays_) {
    if (!InterconnectNameEq(upstream.dst_port, via->name) ||
        upstream.covered_sources != at_load->covered_sources) {
      continue;
    }
    for (std::size_t i = 0; i < 12; ++i) {
      remaining.delays[i] = remaining.delays[i] > upstream.delays[i]
                                ? remaining.delays[i] - upstream.delays[i]
                                : 0;
    }
    break;
  }
  return remaining;
}

std::string SpecifyManager::AskedSourceNet(std::string_view source) const {
  const InterconnectTerminal* asked =
      FindInterconnectTerminal(topology_, source);
  if (asked == nullptr) return InterconnectNetIdOf(source);
  if (IsInterconnectLoadDirection(asked->direction)) return asked->net;
  return {};
}

SpecifyManager::SourceMatch SpecifyManager::CoveredSourceMatch(
    const InterconnectDelay& delay, std::string_view source,
    const std::string& source_net) const {
  SourceMatch match = SourceMatch::kNone;
  for (const auto& covered : delay.covered_sources) {
    if (InterconnectNameEq(covered, source)) return SourceMatch::kNamed;
    if (!source_net.empty() && InterconnectNetIdOf(covered) == source_net)
      match = SourceMatch::kSameNet;
  }
  return match;
}

std::string SpecifyManager::InterconnectNetIdOf(std::string_view name) const {
  if (const auto* terminal = FindInterconnectTerminal(topology_, name))
    return terminal->net;
  if (const auto* net = FindInterconnectNet(topology_, name)) return net->id;
  return {};
}

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
  const std::string kNetId = InterconnectNetIdOf(name);
  if (!kNetId.empty()) {
    for (const auto& delay : interconnect_delays_) {
      if (!DelayLoadCoversReference(delay, kNetId, name)) continue;
      return {true, delay.delays[0], delay.dst_port};
    }
  }
  return {};
}

}  // namespace delta
