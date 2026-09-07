#include "simulator/vcd_dump_state.h"

#include <string>
#include <string_view>
#include <utility>

namespace delta {

VcdDump& VcdDumpState::Dump(VcdFileType type) {
  return type == VcdFileType::kExtended ? extended : four_state;
}

// A writer installed from outside belongs to whoever installed it and covers
// whichever of the two forms that caller decided to write, so both dumps hold
// it and neither owns it. §21.7 gives a source two files to ask for, but a
// driver that built one writer over one file has only that one to offer.
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

// §21.7.2.3: the literal belongs to the 4-state dump, because $dumpfile is the
// task the $version entry reproduces and §21.7.1.1 gives $dumpfile the 4-state
// file. An extended dump the same source opened carries no such entry until a
// $dumpports call spells one.
void VcdDumpState::SetDumpFileLiteral(std::string text) {
  four_state.file_literal = std::move(text);
}

// §21.7.4.1: the version section of the extended file lists the $dumpports
// commands. The dump the commands belong to is the one $dumpports opens, so a
// call that finds it open hands its command to the writer and a call that
// opens it leaves the command here for OpenVcdDump to replay.
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

// §21.7.3.1: $dumpports may be invoked many times, but the execution of all
// $dumpports tasks shall be at the same simulation time. The first call
// records its time; a later call passes only when it matches.
bool VcdDumpState::RegisterDumpportsTime(uint64_t time) {
  if (!have_dumpports_time_) {
    have_dumpports_time_ = true;
    dumpports_time_ = time;
    return true;
  }
  return time == dumpports_time_;
}

// §21.7.1.2: $dumpvars "can be invoked as often as desired throughout the model
// (for example, within various blocks), but the execution of all the $dumpvars
// tasks shall be at the same simulation time". The first call records its time;
// a later call passes only when it matches.
bool VcdDumpState::RegisterDumpvarsTime(uint64_t time) {
  if (!have_dumpvars_time_) {
    have_dumpvars_time_ = true;
    dumpvars_time_ = time;
    return true;
  }
  return time == dumpvars_time_;
}

// §21.7.5: the declared type keyword each dumped name was written with, which
// is what decides the $var declaration. A name never declared with one answers
// kImplicit.
void VcdDumpState::SetVcdVarKind(std::string_view name, DataTypeKind kind) {
  var_kinds_[name] = kind;
}

DataTypeKind VcdDumpState::GetVcdVarKind(std::string_view name) const {
  auto it = var_kinds_.find(name);
  return it != var_kinds_.end() ? it->second : DataTypeKind::kImplicit;
}

// §21.7.4.3.1: a port record's state character comes from the list for the
// port's direction, and the direction is on the port declaration rather than on
// the object the name stands for. A name no declaration covers -- a module-body
// net or variable -- has no direction, and answers the unknown one.
void VcdDumpState::SetVcdPortDirection(std::string_view name,
                                       Direction direction) {
  port_dirs_[name] = direction;
}

Direction VcdDumpState::GetVcdPortDirection(std::string_view name) const {
  auto it = port_dirs_.find(name);
  return it != port_dirs_.end() ? it->second : Direction::kNone;
}

}  // namespace delta
