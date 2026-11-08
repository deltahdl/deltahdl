#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/const_eval.h"
#include "elaborator/disable_iff_resolution.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/interface_property_instance.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

namespace {

UdpDecl* NearestUdpInSearchOrder(const CompilationUnit* unit,
                                 std::string_view name,
                                 const std::vector<std::string>& order,
                                 bool strict, size_t* nearest_pos) {
  UdpDecl* nearest = nullptr;
  for (auto* u : unit->udps) {
    if (u->name != name) continue;
    if (LibraryExcludedBySelectedList(u->library, order, strict)) continue;
    size_t pos = LibrarySearchPosition(u->library, order);
    const bool kDefinesPrototype = nearest != nullptr && pos == *nearest_pos &&
                                   nearest->is_extern && !u->is_extern;
    if (nearest == nullptr || pos < *nearest_pos || kDefinesPrototype) {
      nearest = u;
      *nearest_pos = pos;
    }
  }
  return nearest;
}

}  // namespace

std::optional<UdpDecl*> Elaborator::ResolveUdpUseOverride(
    std::string_view name) const {
  auto clause = cell_clause_use_overrides_.find(std::string(name));
  if (clause == cell_clause_use_overrides_.end()) return std::nullopt;
  if (!CellUseOverrideApplies(clause->second.src_lib, name, unit_)) {
    return std::nullopt;
  }
  const auto& ov = clause->second;
  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  return FindUdpInLibrary(target_lib, ov.use_cell, unit_);
}

UdpDecl* Elaborator::FindUdpByName(std::string_view name) const {
  for (const auto& [path, ulib, ucell] : instance_bind_overrides_) {
    if (config_inst_path_.empty() || path != config_inst_path_) continue;
    std::string_view target_lib = ulib.empty()
                                      ? std::string_view(current_library_)
                                      : std::string_view(ulib);
    return FindUdpInLibrary(target_lib, ucell, unit_);
  }
  if (auto bound = ResolveUdpUseOverride(name); bound.has_value()) {
    return *bound;
  }

  const std::vector<std::string>* selected = SelectedLiblist(name);
  const std::vector<std::string>& order =
      selected == nullptr ? library_order_ : *selected;
  bool strict = selected != nullptr || library_order_strict_;

  size_t nearest_pos = 0;
  UdpDecl* nearest =
      NearestUdpInSearchOrder(unit_, name, order, strict, &nearest_pos);
  if (nearest == nullptr) return nullptr;

  const ModuleDecl* other_kind = FindModule(name);
  if (other_kind == nullptr) return nearest;
  size_t other_pos = LibrarySearchPosition(other_kind->library, order);
  if (other_pos < nearest_pos) return nullptr;
  return nearest;
}

static void TakeForwardUdpDelays(ModuleItem* item, DiagEngine& diag) {
  const auto& params = item->inst_params;
  if (params.empty()) {
    if (item->inst_param_assignment_written) {
      diag.Error(item->loc,
                 "a UDP instance's #( ) holds one or two delays, not none",
                 Subclause("A.5.4"));
    }
    return;
  }
  bool named = std::any_of(params.begin(), params.end(),
                           [](const auto& p) { return !p.first.empty(); });
  if (named) {
    diag.Error(item->loc,
               "a UDP instance takes its delays in order, not a named "
               "assignment",
               Subclause("29.8"));
  } else if (params.size() > 2) {
    diag.Error(item->loc, "UDP instantiation shall have at most two delays",
               Subclause("29.8"));
  }
  if (!named) {
    item->gate_delay = params[0].second;
    if (params.size() > 1) item->gate_delay_fall = params[1].second;
  }
  item->inst_params.clear();
}

static void ReportNamedUdpConnections(const ModuleItem* item,
                                      DiagEngine& diag) {
  bool named = item->inst_wildcard ||
               std::any_of(item->inst_ports.begin(), item->inst_ports.end(),
                           [](const auto& p) { return !p.first.empty(); });
  if (!named) return;
  diag.Error(item->loc,
             "a UDP instance connects its terminals in order, not by name",
             Subclause("29.8"));
}

static void ReportForwardUdpTerminalForms(const ModuleItem* item,
                                          DiagEngine& diag) {
  if (item->inst_port_attr_loc.IsValid()) {
    diag.Error(item->inst_port_attr_loc,
               "a UDP instance's terminal takes no attribute instance",
               Subclause("A.5.4"));
  }
  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    if (item->inst_ports[i].second != nullptr) continue;
    diag.Error(item->loc,
               i == 0 ? "a UDP instance's output terminal is left empty"
                      : "a UDP instance's input terminal is left empty",
               Subclause("A.5.4"));
  }
}

static void ReportForwardUdpArrayRange(const ModuleItem* item,
                                       DiagEngine& diag) {
  if (item->inst_dims.empty()) return;
  if (item->inst_dims[0].second == nullptr) {
    diag.Error(item->loc,
               "an array of instances is declared by a range of two "
               "constant expressions, [lhi:rhi]; a size alone is no range",
               Subclause("28.3.5"));
  }
  if (item->inst_dims.size() > 1) {
    diag.Error(item->loc,
               "an array of instances takes a single range after its "
               "instance identifier, not a second one",
               Subclause("28.3.5"));
  }
}

void Elaborator::ReclassifyForwardUdpInstances(const ModuleDecl* decl) {
  for (auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;

    std::string saved_inst_path = config_inst_path_;
    if (!item->inst_name.empty()) {
      config_inst_path_ =
          HierInstancePath(config_inst_path_, gen_block_path_, item->inst_name);
    }
    UdpDecl* udp = FindUdpByName(item->inst_module);
    config_inst_path_ = std::move(saved_inst_path);
    if (udp == nullptr) continue;

    ReportNamedUdpConnections(item, diag_);
    ReportForwardUdpTerminalForms(item, diag_);
    ReportForwardUdpArrayRange(item, diag_);
    TakeForwardUdpDelays(item, diag_);
    item->kind = ModuleItemKind::kUdpInst;
    item->gate_inst_name = item->inst_name;
    item->inst_name = {};
    item->gate_terminals.clear();
    item->gate_terminals.reserve(item->inst_ports.size());
    for (const auto& [pname, pexpr] : item->inst_ports) {
      item->gate_terminals.push_back(pexpr);
    }
    item->inst_ports.clear();
    item->inst_ports_implicit.clear();
  }
}

static void CheckUdpInstTerminalCount(const ModuleItem* item,
                                      const UdpDecl* decl, DiagEngine& diag) {
  if (decl->input_names.empty()) return;
  size_t declared = decl->input_names.size() + 1;
  if (item->gate_terminals.size() == declared) return;
  diag.Error(
      item->loc,
      std::format("primitive '{}' takes {} terminal(s) but this instance "
                  "connects {}",
                  decl->name, declared, item->gate_terminals.size()),
      Subclause("29.8"));
}

UdpDecl* Elaborator::FindUdpForInstance(const ModuleItem* item) {
  std::string saved_inst_path = config_inst_path_;
  if (!item->gate_inst_name.empty()) {
    config_inst_path_ = HierInstancePath(config_inst_path_, gen_block_path_,
                                         item->gate_inst_name);
  }
  UdpDecl* udp = FindUdpByName(item->inst_module);
  config_inst_path_ = std::move(saved_inst_path);
  return udp;
}

void Elaborator::ElaborateUdpInst(ModuleItem* item, RtlirModule* mod) {
  RecordGateOutputDrivers(item);
  if (const UdpDecl* decl = FindUdpForInstance(item); decl != nullptr) {
    CheckUdpInstTerminalCount(item, decl, diag_);
  } else if (item->udp_undeclared_at_parse) {
    diag_.Error(item->loc,
                std::format("'{}' is instantiated as a user-defined "
                            "primitive, but no primitive has that name",
                            item->inst_module),
                Subclause("29.8"));
    return;
  }

  const ScopeMap kScope = BuildParamScope(mod);
  int64_t offset = 0;
  if (ExpandInstanceArray(item, mod, arena_, kScope, [&](ModuleItem* element) {
        const PackedRange kRange{
            ConstEvalInt(item->inst_range_left, kScope).value_or(0),
            ConstEvalInt(item->inst_range_right, kScope).value_or(0)};
        ElaborateOneUdpInst(element, mod, kRange.IndexAtOffset(offset++));
      }))
    return;

  ElaborateOneUdpInst(item, mod, ConstEvalInt(item->inst_range_left, kScope));
}

void Elaborator::ElaborateOneUdpInst(const ModuleItem* item, RtlirModule* mod,
                                     std::optional<int64_t> index) {
  const UdpDecl* decl = FindUdpForInstance(item);
  if (decl == nullptr) return;
  if (item->gate_terminals.empty()) return;

  RtlirUdpInst inst;
  inst.decl = decl;
  inst.source_item = item;
  inst.name = item->gate_inst_name;
  inst.array_index = index;
  inst.loc = item->loc;
  inst.output = item->gate_terminals.front();
  inst.inputs.assign(item->gate_terminals.begin() + 1,
                     item->gate_terminals.end());
  inst.delay = item->gate_delay;
  inst.delay_fall = item->gate_delay_fall;
  inst.drive_strength0 = item->drive_strength0;
  inst.drive_strength1 = item->drive_strength1;
  mod->udp_insts.push_back(inst);
}

}  // namespace delta
