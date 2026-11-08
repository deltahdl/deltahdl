#include "simulator/vcd_dump_state.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "parser/ast_type.h"
#include "simulator/vcd_writer.h"

namespace delta {

VcdDump& VcdDumpState::Dump(VcdFileType type) {
  return type == VcdFileType::kExtended ? extended : four_state;
}

void VcdDumpState::SetVcdWriter(VcdWriter* vcd) {
  four_state.writer = vcd;
  extended.writer = vcd;
}

void VcdDumpState::SetDumpFileName(std::string name) {
  four_state.file_name = std::move(name);
}

const std::string& VcdDumpState::GetDumpFileName() const {
  return four_state.file_name;
}

void VcdDumpState::SetDumpportsFileName(std::string name) {
  extended.file_name = std::move(name);
}

const std::string& VcdDumpState::GetDumpportsFileName() const {
  return extended.file_name;
}

const std::string& VcdDumpState::GetDumpFileLiteral() const {
  return four_state.file_literal;
}

void VcdDumpState::SetDumpFileLiteral(std::string text) {
  four_state.file_literal = std::move(text);
}

void VcdDumpState::AddDumpportsCommand(std::string text) {
  if (extended.writer != nullptr) {
    extended.writer->AddVersionCommand(text);
    return;
  }
  dumpports_commands.push_back(std::move(text));
}

bool VcdDumpState::RegisterDumpportsScope(const std::string& scope) {
  return dumpports_scopes.insert(scope).second;
}

bool VcdDumpState::RegisterDumpportsFile(const std::string& file) {
  return dumpports_files.insert(file).second;
}

bool VcdDumpState::IsDumpportsFile(const std::string& file) const {
  return dumpports_files.count(file) != 0;
}

bool VcdDumpState::RegisterDumpportsTime(uint64_t time) {
  if (!have_dumpports_time_) {
    have_dumpports_time_ = true;
    dumpports_time_ = time;
    return true;
  }
  return time == dumpports_time_;
}

bool VcdDumpState::RegisterDumpvarsTime(uint64_t time) {
  if (!have_dumpvars_time_) {
    have_dumpvars_time_ = true;
    dumpvars_time_ = time;
    return true;
  }
  return time == dumpvars_time_;
}

void VcdDumpState::SetVcdVarKind(std::string_view name, DataTypeKind kind) {
  var_kinds_[name] = kind;
}

DataTypeKind VcdDumpState::GetVcdVarKind(std::string_view name) const {
  auto it = var_kinds_.find(name);
  return it != var_kinds_.end() ? it->second : DataTypeKind::kImplicit;
}

void VcdDumpState::SetVcdPortDirection(std::string_view name,
                                       Direction direction) {
  port_dirs_[name] = direction;
}

Direction VcdDumpState::GetVcdPortDirection(std::string_view name) const {
  auto it = port_dirs_.find(name);
  return it != port_dirs_.end() ? it->second : Direction::kNone;
}

void VcdDumpState::MarkVcdParameter(std::string_view name) {
  parameters_.insert(name);
}

bool VcdDumpState::IsVcdParameter(std::string_view name) const {
  return parameters_.count(name) != 0;
}

void VcdDumpState::MarkVcdEnumConstant(std::string_view name) {
  enum_constants_.insert(name);
}

bool VcdDumpState::IsVcdEnumConstant(std::string_view name) const {
  return enum_constants_.count(name) != 0;
}

void VcdDumpState::MarkVcdPackage(std::string_view name) {
  packages_.insert(name);
}

bool VcdDumpState::IsVcdPackage(std::string_view name) const {
  return packages_.count(name) != 0;
}

void VcdDumpState::SetVcdScopeKind(const std::string& path, VcdScopeKind kind) {
  scope_kinds_[path] = kind;
}

VcdScopeKind VcdDumpState::GetVcdScopeKind(std::string_view path) const {
  auto it = scope_kinds_.find(std::string(path));
  return it != scope_kinds_.end() ? it->second : VcdScopeKind::kModule;
}

void VcdDumpState::SetVcdPortSource(const std::string& port,
                                    std::string source) {
  port_sources_[port] = std::move(source);
}

std::string_view VcdDumpState::GetVcdPortSource(std::string_view port) const {
  auto it = port_sources_.find(std::string(port));
  return it != port_sources_.end() ? std::string_view(it->second)
                                   : std::string_view();
}

}  // namespace delta
