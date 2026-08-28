// What SimContext hands to a VcdWriter: which of its variables are dumped at
// all, and what §21.7.5 Table 21-11 says each one's $var declaration is to
// claim it is. The writer decides how a declaration and a value change are
// spelled; this file decides which objects reach it and under what type.
#include <algorithm>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {

// §21.7.5: the declared type keyword each dumped name was written with, which
// is what decides the $var declaration below. A name never declared with one
// answers kImplicit.
void SimContext::SetVcdVarKind(std::string_view name, DataTypeKind kind) {
  vcd_var_kinds_[name] = kind;
}

DataTypeKind SimContext::GetVcdVarKind(std::string_view name) const {
  auto it = vcd_var_kinds_.find(name);
  return it != vcd_var_kinds_.end() ? it->second : DataTypeKind::kImplicit;
}

// §21.7.5 (Table 21-11): map a declared SystemVerilog type keyword to the
// VcdDataType whose $var declaration masquerades as the matching 1364-2005
// var_type -- int and enum as integer/32, byte/shortint/longint as reg with
// their fixed sizes, and bit as reg with the total packed width (also covering
// a packed array or structure collapsed to one reg vector). The 4-state
// logic/reg/integer types and every unmapped kind fall through to kNet, which
// keeps the net var_type default established for them by §21.7.2.1/§21.7.2.3;
// real variables are classified separately by their real flag. The lowerer has
// already reduced a typed enum to its base kind and a packed struct to kBit, so
// no enum/struct case appears here. Nor is there a kString case: Table 21-11
// gives a string no row, and SimContext::RegisterVcdSignals drops one before
// registration. kEvent is not a Table 21-11 masquerade at all; see its case.
static VcdDataType VcdDataTypeForDeclKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
      return VcdDataType::kBit;
    case DataTypeKind::kByte:
      return VcdDataType::kByte;
    case DataTypeKind::kShortint:
      return VcdDataType::kShortint;
    case DataTypeKind::kInt:
      return VcdDataType::kInt;
    case DataTypeKind::kLongint:
      return VcdDataType::kLongint;
    case DataTypeKind::kEnum:
      return VcdDataType::kEnum;
    // §21.7.2.1 (Syntax 21-20) lists event among the var_type keywords, so an
    // event is declared as one rather than taking the net default below.
    case DataTypeKind::kEvent:
      return VcdDataType::kEvent;
    default:
      return VcdDataType::kNet;
  }
}

// §21.7.5: what every member of a dumped structure shares -- the one Variable
// the model keeps the whole structure in, and the mapping from a declared
// SystemVerilog type to the 1364-2005 var_type it is dumped as.
struct VcdStructScope {
  Variable* var;
  VcdDataType (*map_kind)(DataTypeKind);
};

// §21.7.5: dump an unpacked structure as a named fork-join block whose member
// elements are declared under the same type mapping as any other object. The
// model keeps the whole structure in one value, so each member is registered
// against that shared variable with the bit range it occupies. A member that is
// itself a structure opens its own nested fork-join block, so a dotted member
// path reads as nested scopes.
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

// §21.7.2.1: memories are not dumped. An unpacked array leaves both a
// whole-array Variable under its own name and per-element shadows named
// name[index] in the variable table; neither is a dumpable object. An
// associative array's backing entry is likewise a memory.
bool SimContext::IsUndumpableVcdName(std::string_view name) const {
  return name.find('[') != std::string_view::npos ||
         FindArrayInfo(name) != nullptr ||
         assoc_arrays_.find(name) != assoc_arrays_.end();
}

void SimContext::RegisterVcdSignals(VcdWriter& vcd) {
  std::vector<std::pair<std::string_view, Variable*>> vars(variables_.begin(),
                                                           variables_.end());
  std::sort(vars.begin(), vars.end(),
            [](const auto& a, const auto& b) { return a.first < b.first; });
  for (const auto& [name, var] : vars) {
    if (IsUndumpableVcdName(name)) continue;
    // §21.7.5: Table 21-11 gives string no row and the subclause defines no
    // mapping outside it, so a string has no 1364-2005 type to masquerade as.
    // §21.7.2.3 rules that a $var's size "specifies how many bits are in the
    // variable", and no size states that for a string, whose length §6.16
    // varies during simulation. Skipping it here rather than mapping it drops
    // the $var declaration and every checkpoint value change together, since
    // VcdWriter writes only what was registered. The declared kind decides it
    // because a string port reaches SetVcdVarKind but not
    // RegisterStringVariable.
    if (GetVcdVarKind(name) == DataTypeKind::kString) continue;
    // §21.7.5: an unpacked structure is not dumped as one object -- it appears
    // as a named fork-join block whose members are the dumped objects. A packed
    // structure is excluded here because the table collapses it to a single reg
    // vector, which the ordinary registration below already produces.
    if (const StructTypeInfo* sinfo = GetVariableStructType(name);
        sinfo != nullptr && !sinfo->is_packed && !sinfo->fields.empty()) {
      RegisterVcdStructScope(vcd, name, {var, VcdDataTypeForDeclKind}, sinfo,
                             0);
      continue;
    }
    VcdSignalSpec spec;
    spec.name = name;
    spec.width = var->value.width;
    spec.var = var;
    // §21.7.2.1: value changes for a real variable are real numbers, so its
    // $var declaration carries the real var_type keyword. The declared type
    // decides this -- the Variable's value only turns real once a real
    // assignment lands, which is after registration. §21.7.5 (Table 21-11): a
    // non-real variable masquerades as the 1364-2005 type its declared
    // SystemVerilog type maps to; an unmapped kind yields kNet, leaving the
    // §21.7.2.3 net var_type default intact.
    spec.data_type = IsRealVariable(name)
                         ? VcdDataType::kReal
                         : VcdDataTypeForDeclKind(GetVcdVarKind(name));
    // §21.7.2.3: the writer picks the $var var_type from the declared net
    // type -- notably a uwire net is recorded as wire -- so a dumped object
    // that is a net carries its net type into the registration.
    if (const Net* net = FindNet(name)) spec.net_type = net->type;
    // §21.7.4.2: in the extended VCD node-information section a port that is a
    // bus prints its index range as the size field, while a single-bit port
    // prints 1. The simulator keeps the resolved bit width of the dumped
    // object -- its declaration's packed range collapsed to a width -- so a
    // multi-bit object supplies the descending range [width-1:0] as the
    // vector_index matching its declaration; a 1-bit object leaves msb/lsb
    // negative and is dumped as a scalar. A real is dumped as one %g value, not
    // a bit vector, so it keeps the scalar size. These bounds are consulted
    // only by the port-node ($dumpports) form; the 4-state $var uses the width.
    if (spec.data_type != VcdDataType::kReal && spec.width > 1) {
      spec.msb = static_cast<int32_t>(spec.width) - 1;
      spec.lsb = 0;
    }
    vcd.RegisterSignal(spec);
  }
}

// §21.7.1 lists two steps for creating a 4-state VCD file: insert the VCD
// system tasks in the SystemVerilog source file "to define the dump file name
// and to specify the variables to be dumped", then run the simulation. Opening
// the file is part of running the source, so this is where it happens.
// Everything §21.7.2.1 orders ahead of the value changes goes out in one go --
// the header sections, the $scope holding the dumped objects, their $var
// declarations and $enddefinitions -- because a task that opens the file
// part-way through a run is already past the point where a header could still
// be written.
//
// An empty top_scope leaves the definitions at the top level rather than
// inside a $scope.
VcdWriter* SimContext::OpenVcdDump(std::string_view top_scope,
                                   bool wait_for_dumpvars) {
  // The writer already installed wins. src/main.cpp's --vcd option opens one
  // before the scheduler runs, so a source's $dumpfile or $dumpvars finds a
  // dump whose header and definitions are already on disk; a second writer
  // over the same context would drop a fresh set of definitions into the
  // middle of that file, and the two would race for the same signal codes.
  if (vcd_writer_ != nullptr) return vcd_writer_;
  auto vcd = std::make_unique<VcdWriter>(dump_file_name_);
  if (!vcd->IsOpen()) return nullptr;
  // §21.7.2.3: the $version section reproduces the $dumpfile call that named
  // the file, its filename argument spelled as it was written. A dump no
  // $dumpfile named leaves that entry out.
  //
  // The $timescale section states the time unit the value change times are
  // given in. Both dump paths declare 1ns, the default GlobalPrecision() whose
  // ticks SimTime counts; a design whose `timescale sets another precision is
  // dumped under a unit it does not use.
  vcd->WriteHeader("1ns", dump_file_literal_);
  if (!top_scope.empty()) vcd->BeginScope(top_scope);
  RegisterVcdSignals(*vcd);
  if (!top_scope.empty()) vcd->EndScope();
  vcd->EndDefinitions();
  if (wait_for_dumpvars) {
    // §21.7.1.3: "Executing the $dumpvars task causes the value change dumping
    // to start at the end of the current simulation time unit", so nothing is
    // recorded until that task runs.
    vcd->ArmDumpvarsStart();
  } else {
    // A dump opened by something other than a VCD system task has no $dumpvars
    // coming to start it, so it records every object from time 0.
    vcd->WriteTimestamp(0);
    vcd->DumpAllValues();
  }
  owned_vcd_writer_ = std::move(vcd);
  vcd_writer_ = owned_vcd_writer_.get();
  // §21.7.2.4: each simulation time unit that changed a dumped value
  // contributes its simulation_time command and the value changes under it, so
  // the recording runs once per time step for the rest of the run. The
  // callback reads the writer back out of the context rather than capturing
  // it, so it stops on its own once CloseVcdDump has closed the dump.
  scheduler_.AddPostTimestepCallback([this]() {
    if (vcd_writer_ == nullptr) return;
    vcd_writer_->WriteTimestamp(CurrentTime().ticks);
    vcd_writer_->DumpChangedValues(0);
  });
  return vcd_writer_;
}

// §21.7.1: the dump a source creates for itself. §21.7.1.1 names the file
// through $dumpfile and defaults it to "dump.vcd" when the source specifies no
// filename, and the dumped objects sit in the $scope of the top module the run
// elaborated (§21.7.2.3).
VcdWriter* SimContext::OpenVcdDumpFromTask() {
  return OpenVcdDump(current_scope_name_, /*wait_for_dumpvars=*/true);
}

// §21.7.3.6.1: an extended VCD file records the final simulation time as it is
// closed. Closing here rather than at destruction is what flushes the buffered
// value changes to disk while the context is still alive to be read back.
void SimContext::CloseVcdDump() {
  if (vcd_writer_ == nullptr) return;
  vcd_writer_->WriteVcdClose(CurrentTime().ticks);
  owned_vcd_writer_.reset();
  vcd_writer_ = nullptr;
}
}  // namespace delta
