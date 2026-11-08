#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/vcd_writer.h"

namespace delta {

struct VcdDumpState {
  VcdDump four_state{"dump.vcd"};
  VcdDump extended{"dumpports.vcd"};

  VcdDump& Dump(VcdFileType type);

  void SetVcdWriter(VcdWriter* vcd);
  VcdWriter* GetVcdWriter() { return four_state.writer; }
  VcdWriter* GetDumpportsWriter() { return extended.writer; }

  void SetDumpFileName(std::string name);
  const std::string& GetDumpFileName() const;

  void SetDumpportsFileName(std::string name);
  const std::string& GetDumpportsFileName() const;

  void SetDumpFileLiteral(std::string text);
  const std::string& GetDumpFileLiteral() const;

  std::unordered_set<std::string> dumpports_scopes;
  std::unordered_set<std::string> dumpports_files;
  std::vector<std::string> dumpports_commands;

  bool RegisterDumpportsScope(const std::string& scope);
  bool RegisterDumpportsFile(const std::string& file);
  bool IsDumpportsFile(const std::string& file) const;
  bool HasDumpportsFiles() const { return !dumpports_files.empty(); }
  void AddDumpportsCommand(std::string text);

  bool RegisterDumpportsTime(uint64_t time);
  bool RegisterDumpvarsTime(uint64_t time);

  void SetVcdVarKind(std::string_view name, DataTypeKind kind);
  DataTypeKind GetVcdVarKind(std::string_view name) const;
  void SetVcdPortDirection(std::string_view name, Direction direction);
  Direction GetVcdPortDirection(std::string_view name) const;
  void MarkVcdParameter(std::string_view name);
  bool IsVcdParameter(std::string_view name) const;
  void MarkVcdEnumConstant(std::string_view name);
  bool IsVcdEnumConstant(std::string_view name) const;
  void MarkVcdPackage(std::string_view name);
  bool IsVcdPackage(std::string_view name) const;
  void SetVcdScopeKind(const std::string& path, VcdScopeKind kind);
  VcdScopeKind GetVcdScopeKind(std::string_view path) const;
  void SetVcdPortSource(const std::string& port, std::string source);
  std::string_view GetVcdPortSource(std::string_view port) const;

 private:
  bool have_dumpports_time_ = false;
  uint64_t dumpports_time_ = 0;
  bool have_dumpvars_time_ = false;
  uint64_t dumpvars_time_ = 0;

  std::unordered_map<std::string_view, DataTypeKind> var_kinds_;
  std::unordered_map<std::string_view, Direction> port_dirs_;
  std::unordered_set<std::string_view> parameters_;
  std::unordered_set<std::string_view> enum_constants_;
  std::unordered_set<std::string_view> packages_;
  std::unordered_map<std::string, VcdScopeKind> scope_kinds_;
  std::unordered_map<std::string, std::string> port_sources_;
};

}  // namespace delta
