#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"
#include "simulator/vcd_dump_state.h"
#include "simulator/vcd_writer.h"

namespace delta {

struct VcdStructScope {
  Variable* var;
  VcdDataType (*map_kind)(DataTypeKind);
};

static void RegisterVcdStructScope(VcdWriter& vcd, std::string_view scope_name,
                                   const VcdStructScope& scope,
                                   const StructTypeInfo* info,
                                   uint32_t base_offset) {
  vcd.BeginScope(scope_name, VcdScopeKind::kFork);
  for (const auto& field : info->fields) {
    if (field.nested != nullptr) {
      RegisterVcdStructScope(vcd, field.name, scope, field.nested,
                             base_offset + field.bit_offset);
      continue;
    }
    VcdSignalSpec spec;
    spec.name = field.name;
    spec.width = field.width;
    spec.var = scope.var;
    spec.data_type = scope.map_kind(field.type_kind);
    spec.bit_offset = base_offset + field.bit_offset;
    spec.is_field = true;
    vcd.RegisterSignal(spec);
  }
  vcd.EndScope();
}

bool SimContext::IsUndumpableVcdName(std::string_view name) const {
  return name.find('[') != std::string_view::npos ||
         FindArrayInfo(name) != nullptr ||
         assoc_arrays_.find(name) != assoc_arrays_.end() ||
         vcd_.IsVcdEnumConstant(name);
}

static std::string_view EnterVcdInstanceScope(
    VcdWriter& vcd, const VcdDumpState& state,
    std::vector<std::string_view>& open, std::string_view name) {
  std::vector<std::string_view> path;
  size_t start = 0;
  for (size_t dot = name.find('.'); dot != std::string_view::npos;
       dot = name.find('.', start)) {
    path.push_back(name.substr(start, dot - start));
    start = dot + 1;
  }
  size_t common = 0;
  while (common < open.size() && common < path.size() &&
         open[common] == path[common]) {
    ++common;
  }
  for (; open.size() > common; open.pop_back()) vcd.EndScope();
  for (; open.size() < path.size(); open.push_back(path[open.size()])) {
    std::string_view level = path[open.size()];
    size_t end = static_cast<size_t>(level.data() - name.data()) + level.size();
    vcd.BeginScope(level, state.GetVcdScopeKind(name.substr(0, end)));
  }
  return name.substr(start);
}

static void SetVcdPortRange(VcdSignalSpec& spec) {
  if (spec.data_type != VcdDataType::kReal && spec.width > 1) {
    spec.msb = static_cast<int32_t>(spec.width) - 1;
    spec.lsb = 0;
  }
}

static VcdDataType DeclaredVcdDataType(const VcdDumpState& state,
                                       std::string_view name, bool is_real) {
  if (state.IsVcdParameter(name)) return VcdDataType::kParameter;
  if (is_real) return VcdDataType::kReal;
  return VcdDataTypeForDeclKind(state.GetVcdVarKind(name));
}

bool SimContext::IsVcdPackageVariable(std::string_view name) const {
  size_t dot = name.find('.');
  return dot != std::string_view::npos &&
         vcd_.IsVcdPackage(name.substr(0, dot));
}

void SimContext::RegisterVcdSignals(VcdWriter& vcd) {
  RegisterVcdSignalsOf(vcd, false);
}

void SimContext::RegisterVcdPackageSignals(VcdWriter& vcd) {
  RegisterVcdSignalsOf(vcd, true);
}

void SimContext::RegisterVcdSignalsOf(VcdWriter& vcd, bool packages) {
  std::vector<std::pair<std::string_view, Variable*>> vars(variables_.begin(),
                                                           variables_.end());
  std::sort(vars.begin(), vars.end(),
            [](const auto& a, const auto& b) { return a.first < b.first; });
  std::vector<std::string_view> open_scopes;
  for (const auto& [name, var] : vars) {
    if (IsUndumpableVcdName(name) || IsVcdPackageVariable(name) != packages)
      continue;
    if (vcd_.GetVcdVarKind(name) == DataTypeKind::kString) continue;
    std::string_view ref_name =
        EnterVcdInstanceScope(vcd, vcd_, open_scopes, name);
    if (const StructTypeInfo* sinfo = GetVariableStructType(name);
        sinfo != nullptr && !sinfo->is_packed && !sinfo->fields.empty()) {
      RegisterVcdStructScope(vcd, ref_name, {var, VcdDataTypeForDeclKind},
                             sinfo, 0);
      continue;
    }
    VcdSignalSpec spec;
    spec.name = name;
    spec.ref_name = ref_name;
    spec.width = var->value.width;
    spec.var = var;
    spec.data_type = DeclaredVcdDataType(vcd_, name, IsRealVariable(name));
    spec.direction = vcd_.GetVcdPortDirection(name);
    if (const Net* net = FindNet(name)) {
      spec.net_type = net->type;
      spec.net = net;
    }
    if (std::string_view source = vcd_.GetVcdPortSource(name); !source.empty())
      spec.source_net = FindNet(source);
    SetVcdPortRange(spec);
    vcd.RegisterSignal(spec);
  }
  for (; !open_scopes.empty(); open_scopes.pop_back()) vcd.EndScope();
}

VcdWriter* SimContext::OpenVcdDump(std::string_view top_scope,
                                   bool wait_for_dumpvars, VcdFileType type) {
  VcdDump& dump = vcd_.Dump(type);
  if (dump.writer != nullptr) return dump.writer;
  auto vcd = std::make_unique<VcdWriter>(dump.file_name);
  if (!vcd->IsOpen()) return nullptr;
  if (wait_for_dumpvars) vcd->BufferDeclarations();
  if (type == VcdFileType::kExtended) {
    vcd->SetExtended();
    vcd->SetExtendedPortNodes();
    vcd->BufferDeclarations();
  }
  std::string timescale = "1";
  timescale += TimeUnitStr(GlobalPrecision());
  vcd->WriteHeader(timescale, dump.file_literal);
  if (type == VcdFileType::kExtended) {
    for (const auto& command : vcd_.dumpports_commands) {
      vcd->AddVersionCommand(command);
    }
    vcd_.dumpports_commands.clear();
  }
  vcd->SetTopScope(top_scope);
  if (!top_scope.empty()) vcd->BeginScope(top_scope);
  RegisterVcdSignals(*vcd);
  if (!top_scope.empty()) vcd->EndScope();
  RegisterVcdPackageSignals(*vcd);
  vcd->EndDefinitions();
  if (wait_for_dumpvars) {
    vcd->ArmDumpvarsStart();
  } else {
    vcd->WriteTimestamp(0);
    vcd->DumpAllValues();
  }
  dump.owned = std::move(vcd);
  dump.writer = dump.owned.get();
  scheduler_.AddPostTimestepCallback(
      [this, type]() { RecordVcdTimestep(vcd_.Dump(type).writer); });
  return dump.writer;
}

VcdWriter* SimContext::OpenVcdDumpFromTask(VcdFileType type) {
  return OpenVcdDump(current_scope_name_, true, type);
}

void SimContext::RecordVcdTimestep(VcdWriter* writer) {
  if (writer == nullptr) return;
  writer->WriteTimestamp(CurrentTime().ticks);
  writer->DumpChangedValues(0);
}

void SimContext::CloseOneVcdDump(VcdDump& dump) {
  if (dump.writer == nullptr) return;
  RecordVcdTimestep(dump.writer);
  dump.writer->WriteVcdClose(CurrentTime().ticks);
  dump.owned.reset();
  dump.writer = nullptr;
}

void SimContext::CloseVcdDump() {
  VcdWriter* four_state = vcd_.four_state.writer;
  CloseOneVcdDump(vcd_.four_state);
  if (vcd_.extended.writer == four_state) {
    vcd_.extended.writer = nullptr;
    vcd_.extended.owned.reset();
    return;
  }
  CloseOneVcdDump(vcd_.extended);
}

void SimContext::CloseDumpportsDump() { CloseOneVcdDump(vcd_.extended); }
}  // namespace delta
