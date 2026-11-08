#pragma once

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <memory>
#include <ostream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

struct Net;
struct Variable;
enum class DataTypeKind : uint8_t;
enum class Direction : uint8_t;

enum class VcdDataType : uint8_t {
  kNet,
  kBit,
  kLogic,
  kInt,
  kShortint,
  kLongint,
  kByte,
  kEnum,
  kReal,
  kReg,
  kInteger,
  kTime,
  kEvent,
  kParameter,
};

VcdDataType VcdDataTypeForDeclKind(DataTypeKind kind);

enum class VcdScopeKind : uint8_t {
  kModule,
  kTask,
  kFunction,
  kBegin,
  kFork,
};

enum class VcdFileType : uint8_t {
  kFourState,
  kExtended,
};

enum class VcdVarSelection : uint8_t {
  kEveryObject,
  kListedObjects,
  kEveryObjectByTask,
};

struct VcdSignal {
  std::string_view name;
  uint32_t width = 1;
  Variable* var = nullptr;
  char ident = '!';
  NetType net_type = NetType::kWire;
  Direction direction{};
  VcdDataType data_type = VcdDataType::kNet;
  int32_t msb = -1;
  int32_t lsb = -1;
  uint32_t port_id = 0;
  const Net* net = nullptr;
  const Net* source_net = nullptr;
  uint32_t bit_offset = 0;
  bool is_field = false;
  bool dump_selected = false;
  std::string prev_digits;
  bool has_prev_digits = false;
  std::vector<Logic4Word> prev_words;
  bool has_prev_words = false;
};

struct VcdSignalSpec {
  std::string_view name;
  uint32_t width = 1;
  Variable* var = nullptr;
  NetType net_type = NetType::kWire;
  int32_t msb = -1;
  int32_t lsb = -1;
  VcdDataType data_type = VcdDataType::kNet;
  uint32_t bit_offset = 0;
  bool is_field = false;
  const Net* net = nullptr;
  Direction direction{};
  std::string_view ref_name = {};
  const Net* source_net = nullptr;
};

char VcdBitChar(const VcdSignal& sig, int32_t bit);
void WritePortVarDecl(std::ostream& ofs, const VcdSignal& sig,
                      std::string_view name);

class VcdWriter {
 public:
  explicit VcdWriter(const std::string& filename);
  ~VcdWriter();

  VcdWriter(const VcdWriter&) = delete;
  VcdWriter& operator=(const VcdWriter&) = delete;

  bool IsOpen() const { return ofs_.is_open(); }

  void WriteHeader(std::string_view timescale,
                   std::string_view dumpfile_literal = {});
  void BeginScope(std::string_view name,
                  VcdScopeKind kind = VcdScopeKind::kModule);
  void EndScope();
  void WriteComment(std::string_view text);
  void RegisterSignal(const VcdSignalSpec& spec);
  void RegisterSignal(std::string_view name, uint32_t width, Variable* var) {
    RegisterSignal(VcdSignalSpec{name, width, var});
  }
  void EndDefinitions();

  void WriteTimestamp(uint64_t time);
  void DumpAllValues();
  void DumpAllValues(uint64_t time);
  void DumpSelectedValues(const std::vector<std::string_view>& names);
  void DumpScopeSelectedValues(const std::vector<std::string_view>& names,
                               uint64_t level);
  void DumpScopeSelectedValues(const std::vector<std::string_view>& names,
                               uint64_t level, uint64_t time);
  void DumpChangedValues(uint64_t prev_time);
  void EmitPendingPortStartCheckpoint();

  void DumpAll();
  void DumpAll(uint64_t time);

  void DumpOff();
  void DumpOff(uint64_t time);
  void DumpOn();
  void DumpOn(uint64_t time);

  bool IsEnabled() const { return enabled_; }

  void ArmDumpvarsStart() { dump_started_ = false; }

  void SetTopScope(std::string_view name) { top_scope_ = std::string(name); }

  void Flush();

  void SetSizeLimit(uint64_t limit_bytes) { size_limit_ = limit_bytes; }

  void SetExtended() { extended_ = true; }

  bool IsExtended() const { return extended_; }

  void SchedulePortDumpStart(std::vector<std::string> scopes, uint64_t time);

  void SetExtendedPortNodes() { port_nodes_ = true; }

  void BufferDeclarations();
  void AddVersionCommand(std::string_view text);

  void WriteVcdClose(uint64_t final_time);

 private:
  void EnsureTimestamp(uint64_t time);
  void WriteScalarChange(const VcdSignal& sig);
  void WriteVectorChange(const VcdSignal& sig);
  void WriteRealChange(const VcdSignal& sig);
  void WritePortValueChange(const VcdSignal& sig);
  void WriteSignalChange(VcdSignal& sig);
  void WriteSignalAllX(const VcdSignal& sig);
  bool AtSizeLimit();

  std::ostream& Out() {
    return buffer_decls_ ? static_cast<std::ostream&>(decl_buf_)
                         : static_cast<std::ostream&>(ofs_);
  }
  void FlushDeclarations();
  enum class HeldDeclKind : uint8_t { kScope, kUpscope, kVar };
  struct HeldDecl {
    size_t begin;
    size_t end;
    HeldDeclKind kind;
    size_t signal;
  };
  void HoldDecl(size_t begin, HeldDeclKind kind, size_t signal = 0);
  std::vector<bool> KeptHeldDecls() const;
  std::string SelectedDeclarations(const std::string& text) const;

  std::ofstream ofs_;
  std::ostringstream decl_buf_;
  bool buffer_decls_ = false;
  std::vector<HeldDecl> held_decls_;
  size_t version_commands_at_ = 0;
  std::vector<std::string> version_commands_;
  std::vector<VcdSignal> signals_;
  char next_ident_ = '!';
  bool enabled_ = true;
  bool dump_started_ = true;
  std::string top_scope_;
  VcdVarSelection var_selection_ = VcdVarSelection::kEveryObject;

  bool DumpsObject(const VcdSignal& sig) const {
    return var_selection_ != VcdVarSelection::kListedObjects ||
           sig.dump_selected;
  }

  void NarrowSelectionToListed() {
    if (port_nodes_) return;
    if (var_selection_ != VcdVarSelection::kEveryObjectByTask)
      var_selection_ = VcdVarSelection::kListedObjects;
  }
  uint64_t last_time_ = 0;
  bool have_time_ = false;
  bool header_written_ = false;
  uint64_t size_limit_ = 0;
  bool limit_reached_ = false;
  bool extended_ = false;
  bool port_nodes_ = false;
  uint32_t next_port_id_ = 0;
  bool port_start_pending_ = false;
  uint64_t port_start_time_ = 0;
  std::vector<std::string> port_scopes_;
  bool port_selection_active_ = false;
  bool port_start_scheduled_ = false;
};

struct VcdDump {
  explicit VcdDump(std::string default_name)
      : file_name(std::move(default_name)) {}
  std::unique_ptr<VcdWriter> owned;
  VcdWriter* writer = nullptr;
  std::string file_name;
  std::string file_literal;
};

}  // namespace delta
