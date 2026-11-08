#include "simulator/vcd_writer.h"

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <ctime>
#include <iosfwd>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace delta {

VcdDataType VcdDataTypeForDeclKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
      return VcdDataType::kBit;
    case DataTypeKind::kLogic:
      return VcdDataType::kLogic;
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
    case DataTypeKind::kReg:
      return VcdDataType::kReg;
    case DataTypeKind::kInteger:
      return VcdDataType::kInteger;
    case DataTypeKind::kTime:
      return VcdDataType::kTime;
    case DataTypeKind::kEvent:
      return VcdDataType::kEvent;
    default:
      return VcdDataType::kNet;
  }
}

static std::string CurrentDateText() {
  std::time_t now = std::time(nullptr);
  std::tm tm_buf{};
  localtime_r(&now, &tm_buf);
  char buf[64];
  std::strftime(buf, sizeof(buf), "%b %d, %Y %H:%M:%S", &tm_buf);
  return buf;
}

VcdWriter::VcdWriter(const std::string& filename) : ofs_(filename) {}

VcdWriter::~VcdWriter() {
  FlushDeclarations();
  if (ofs_.is_open()) ofs_.close();
}

void VcdWriter::BufferDeclarations() { buffer_decls_ = true; }

void VcdWriter::AddVersionCommand(std::string_view text) {
  if (!buffer_decls_) return;
  version_commands_.emplace_back(text);
}

void VcdWriter::FlushDeclarations() {
  if (!buffer_decls_) return;
  buffer_decls_ = false;
  if (!ofs_.is_open()) return;
  std::string text = SelectedDeclarations(decl_buf_.str());
  decl_buf_.str(std::string());
  held_decls_.clear();
  std::string commands;
  for (const auto& command : version_commands_) {
    commands += "  " + command + "\n";
  }
  text.insert(version_commands_at_ <= text.size() ? version_commands_at_ : 0,
              commands);
  ofs_ << text;
}

void VcdWriter::WriteHeader(std::string_view timescale,
                            std::string_view dumpfile_literal) {
  if (!ofs_.is_open()) return;
  std::ostream& out = Out();
  out << "$date\n  " << CurrentDateText() << "\n$end\n";
  out << "$version\n  DeltaHDL 0.1.0\n";
  if (!dumpfile_literal.empty()) {
    out << "  $dumpfile(" << dumpfile_literal << ")\n";
  }
  if (buffer_decls_) {
    version_commands_at_ = static_cast<size_t>(decl_buf_.tellp());
  }
  out << "$end\n";
  out << "$timescale\n  " << timescale << "\n$end\n";
  header_written_ = true;
}

static const char* VcdScopeKeyword(VcdScopeKind kind) {
  switch (kind) {
    case VcdScopeKind::kTask:
      return "task";
    case VcdScopeKind::kFunction:
      return "function";
    case VcdScopeKind::kBegin:
      return "begin";
    case VcdScopeKind::kFork:
      return "fork";
    case VcdScopeKind::kModule:
      break;
  }
  return "module";
}

void VcdWriter::BeginScope(std::string_view name, VcdScopeKind kind) {
  if (!ofs_.is_open()) return;
  auto begin = static_cast<size_t>(decl_buf_.tellp());
  Out() << "$scope " << VcdScopeKeyword(kind) << " " << name << " $end\n";
  HoldDecl(begin, HeldDeclKind::kScope);
}

void VcdWriter::EndScope() {
  if (!ofs_.is_open()) return;
  auto begin = static_cast<size_t>(decl_buf_.tellp());
  Out() << "$upscope $end\n";
  HoldDecl(begin, HeldDeclKind::kUpscope);
}

void VcdWriter::HoldDecl(size_t begin, HeldDeclKind kind, size_t signal) {
  if (!buffer_decls_) return;
  held_decls_.push_back(
      {begin, static_cast<size_t>(decl_buf_.tellp()), kind, signal});
}

std::vector<bool> VcdWriter::KeptHeldDecls() const {
  std::vector<bool> keep(held_decls_.size(), true);
  std::vector<std::pair<size_t, bool>> open;
  auto mark_used = [&open]() {
    if (!open.empty()) open.back().second = true;
  };
  for (size_t i = 0; i < held_decls_.size(); ++i) {
    const HeldDecl& d = held_decls_[i];
    if (d.kind == HeldDeclKind::kScope) {
      open.emplace_back(i, false);
    } else if (d.kind == HeldDeclKind::kVar) {
      keep[i] = DumpsObject(signals_[d.signal]);
      if (keep[i]) mark_used();
    } else if (!open.empty()) {
      auto [scope, used] = open.back();
      open.pop_back();
      keep[scope] = keep[i] = used;
      if (used) mark_used();
    }
  }
  return keep;
}

std::string VcdWriter::SelectedDeclarations(const std::string& text) const {
  if (var_selection_ != VcdVarSelection::kListedObjects) return text;
  std::vector<bool> keep = KeptHeldDecls();
  std::string out;
  size_t at = 0;
  for (size_t i = 0; i < held_decls_.size(); ++i) {
    if (keep[i]) continue;
    out.append(text, at, held_decls_[i].begin - at);
    at = held_decls_[i].end;
  }
  out.append(text, at);
  return out;
}

static const char* VcdVarTypeKeyword(const VcdSignal& sig) {
  if (sig.var && sig.var->value.is_real) return "real";
  return "wire";
}

static const char* VcdDataTypeKeyword(VcdDataType type) {
  switch (type) {
    case VcdDataType::kBit:
    case VcdDataType::kLogic:
    case VcdDataType::kShortint:
    case VcdDataType::kLongint:
    case VcdDataType::kByte:
    case VcdDataType::kReg:
      return "reg";
    case VcdDataType::kInt:
    case VcdDataType::kEnum:
    case VcdDataType::kInteger:
      return "integer";
    case VcdDataType::kTime:
      return "time";
    case VcdDataType::kReal:
      return "real";
    case VcdDataType::kEvent:
      return "event";
    case VcdDataType::kParameter:
      return "parameter";
    case VcdDataType::kNet:
      break;
  }
  return "wire";
}

static uint32_t VcdDataTypeSize(VcdDataType type, uint32_t width) {
  switch (type) {
    case VcdDataType::kInt:
    case VcdDataType::kEnum:
    case VcdDataType::kInteger:
      return 32;
    case VcdDataType::kTime:
      return 64;
    case VcdDataType::kShortint:
      return 16;
    case VcdDataType::kLongint:
      return 64;
    case VcdDataType::kByte:
      return 8;
    case VcdDataType::kEvent:
      return 0;
    case VcdDataType::kBit:
    case VcdDataType::kLogic:
    case VcdDataType::kReg:
    case VcdDataType::kReal:
    case VcdDataType::kParameter:
    case VcdDataType::kNet:
      break;
  }
  return width;
}

static VcdSignal MakeVcdSignalFields(const VcdSignalSpec& spec) {
  VcdSignal sig;
  sig.name = spec.name;
  sig.width = spec.width;
  sig.var = spec.var;
  sig.net_type = spec.net_type;
  sig.direction = spec.direction;
  sig.data_type = spec.data_type;
  sig.msb = spec.msb;
  sig.lsb = spec.lsb;
  sig.bit_offset = spec.bit_offset;
  sig.is_field = spec.is_field;
  sig.net = spec.net;
  sig.source_net = spec.source_net;
  return sig;
}

static void AssignVcdSignalCodes(VcdSignal& sig, char& next_ident,
                                 uint32_t& next_port_id) {
  sig.ident = next_ident++;
  sig.port_id = next_port_id++;
  if (next_ident > '~') next_ident = '!';
}

static VcdSignal MakeVcdSignal(const VcdSignalSpec& spec, char& next_ident,
                               uint32_t& next_port_id) {
  VcdSignal sig = MakeVcdSignalFields(spec);
  AssignVcdSignalCodes(sig, next_ident, next_port_id);
  return sig;
}

static void WriteVarDecl(std::ostream& ofs, const VcdSignal& sig,
                         std::string_view name, uint32_t width) {
  const char* keyword = sig.data_type == VcdDataType::kNet
                            ? VcdVarTypeKeyword(sig)
                            : VcdDataTypeKeyword(sig.data_type);
  uint32_t size = VcdDataTypeSize(sig.data_type, width);
  ofs << "$var " << keyword << " " << size << " " << sig.ident << " " << name
      << " $end\n";
}

static void WriteSignalVarDecl(std::ostream& ofs, const VcdSignal& sig,
                               std::string_view name, uint32_t width,
                               bool port_nodes) {
  if (port_nodes) {
    WritePortVarDecl(ofs, sig, name);
    return;
  }
  WriteVarDecl(ofs, sig, name, width);
}

void VcdWriter::RegisterSignal(const VcdSignalSpec& spec) {
  if (spec.name.find('[') != std::string_view::npos) return;
  VcdSignal sig = MakeVcdSignal(spec, next_ident_, next_port_id_);
  signals_.push_back(sig);
  if (!ofs_.is_open()) return;
  auto begin = static_cast<size_t>(decl_buf_.tellp());
  WriteSignalVarDecl(Out(), sig,
                     spec.ref_name.empty() ? spec.name : spec.ref_name,
                     spec.width, port_nodes_);
  HoldDecl(begin, HeldDeclKind::kVar, signals_.size() - 1);
}

void VcdWriter::WriteComment(std::string_view text) {
  if (!ofs_.is_open()) return;
  Out() << "$comment\n  " << text << "\n$end\n";
}

void VcdWriter::EndDefinitions() {
  if (!ofs_.is_open()) return;
  Out() << "$enddefinitions $end\n";
}

bool VcdWriter::AtSizeLimit() {
  if (size_limit_ == 0) return false;
  if (limit_reached_) return true;
  if (!ofs_.is_open()) return false;
  std::streampos pos = ofs_.tellp();
  if (pos == std::streampos(-1)) return false;
  auto size = static_cast<uint64_t>(pos);
  if (buffer_decls_) size += static_cast<uint64_t>(decl_buf_.tellp());
  if (size < size_limit_) return false;
  WriteComment("Dump limit of " + std::to_string(size_limit_) +
               " bytes reached, dumping stopped.");
  limit_reached_ = true;
  return true;
}

void VcdWriter::WriteTimestamp(uint64_t time) {
  FlushDeclarations();
  if (!ofs_.is_open() || !enabled_ || !dump_started_) return;
  if (AtSizeLimit()) return;
  if (have_time_ && time == last_time_) return;
  Out() << "#" << time << "\n";
  last_time_ = time;
  have_time_ = true;
}

void VcdWriter::EnsureTimestamp(uint64_t time) {
  if (!ofs_.is_open()) return;
  if (have_time_ && time == last_time_) return;
  Out() << "#" << time << "\n";
  last_time_ = time;
  have_time_ = true;
}

static char LogicBitToChar(bool aval, bool bval) {
  if (!bval && !aval) return '0';
  if (!bval && aval) return '1';
  if (bval && aval) return 'x';
  return 'z';
}

static char VcdLeftExtendFill(char digit) {
  if (digit == 'x') return 'x';
  if (digit == 'z') return 'z';
  return '0';
}

char VcdBitChar(const VcdSignal& sig, int32_t i) {
  uint32_t abs_bit = static_cast<uint32_t>(i) + sig.bit_offset;
  uint32_t word_idx = abs_bit / 64;
  uint32_t bit_idx = abs_bit % 64;
  uint64_t mask = uint64_t{1} << bit_idx;
  bool a = false;
  bool b = false;
  if (word_idx < sig.var->value.nwords) {
    a = (sig.var->value.words[word_idx].aval & mask) != 0;
    b = (sig.var->value.words[word_idx].bval & mask) != 0;
  }
  return LogicBitToChar(a, b);
}

static std::string VcdSignalDigits(const VcdSignal& sig) {
  std::string digits;
  digits.reserve(sig.width);
  for (int32_t i = static_cast<int32_t>(sig.width) - 1; i >= 0; --i) {
    digits.push_back(VcdBitChar(sig, i));
  }
  return digits;
}

void VcdWriter::WriteScalarChange(const VcdSignal& sig) {
  if (!sig.var) return;
  Out() << VcdBitChar(sig, 0) << sig.ident << "\n";
}

void VcdWriter::WriteVectorChange(const VcdSignal& sig) {
  if (!sig.var) return;
  std::string digits = VcdSignalDigits(sig);
  size_t start = 0;
  while (start + 1 < digits.size() &&
         digits[start] == VcdLeftExtendFill(digits[start + 1])) {
    ++start;
  }
  Out() << 'b' << (digits.c_str() + start) << ' ' << sig.ident << "\n";
}

void VcdWriter::WriteRealChange(const VcdSignal& sig) {
  if (!sig.var) return;
  double d = RealVecToDouble(sig.var->value);
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%.16g", d);
  Out() << "r" << buf << " " << sig.ident << "\n";
}

static void RecordEmittedValue(VcdSignal& sig) {
  if (sig.is_field) {
    sig.prev_digits = VcdSignalDigits(sig);
    sig.has_prev_digits = true;
    return;
  }
  const Logic4Vec& value = sig.var->value;
  sig.prev_words.assign(value.words, value.words + value.nwords);
  sig.has_prev_words = true;
}

void VcdWriter::WriteSignalChange(VcdSignal& sig) {
  if (sig.var && sig.var->is_event) {
    if (sig.var->triggered_ticks == last_time_) {
      Out() << '1' << sig.ident << "\n";
    }
    return;
  }
  if (sig.var && sig.var->value.is_real) {
    WriteRealChange(sig);
  } else if (port_nodes_) {
    WritePortValueChange(sig);
  } else if (sig.width == 1) {
    WriteScalarChange(sig);
  } else {
    WriteVectorChange(sig);
  }
  if (sig.var) RecordEmittedValue(sig);
}

void VcdWriter::WriteSignalAllX(const VcdSignal& sig) {
  if (sig.data_type == VcdDataType::kEvent) return;
  if (sig.var && sig.var->value.is_real) {
    Out() << "r0 " << sig.ident << "\n";
  } else if (sig.width == 1) {
    Out() << "x" << sig.ident << "\n";
  } else {
    Out() << "bx " << sig.ident << "\n";
  }
}

static const char* CheckpointKeyword(bool port_nodes, const char* four_state,
                                     const char* extended) {
  return port_nodes ? extended : four_state;
}

static bool HasValueChanged(const VcdSignal& sig) {
  if (sig.is_field) {
    return !sig.has_prev_digits || VcdSignalDigits(sig) != sig.prev_digits;
  }
  if (!sig.has_prev_words) return true;
  const Logic4Vec& value = sig.var->value;
  if (sig.prev_words.size() < value.nwords) return true;
  for (uint32_t w = 0; w < value.nwords; ++w) {
    if (value.words[w].aval != sig.prev_words[w].aval ||
        value.words[w].bval != sig.prev_words[w].bval) {
      return true;
    }
  }
  return false;
}

void VcdWriter::DumpAllValues() {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  dump_started_ = true;
  var_selection_ = VcdVarSelection::kEveryObjectByTask;
  Out() << CheckpointKeyword(port_nodes_, "$dumpvars", "$dumpports") << "\n";
  for (auto& sig : signals_) {
    WriteSignalChange(sig);
  }
  Out() << "$end\n";
}

void VcdWriter::DumpSelectedValues(const std::vector<std::string_view>& names) {
  FlushDeclarations();
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  dump_started_ = true;
  NarrowSelectionToListed();
  Out() << CheckpointKeyword(port_nodes_, "$dumpvars", "$dumpports") << "\n";
  for (auto& sig : signals_) {
    bool wanted = false;
    for (auto name : names) {
      if (sig.name == name) {
        wanted = true;
        break;
      }
    }
    if (!wanted) continue;
    sig.dump_selected = true;
    WriteSignalChange(sig);
  }
  Out() << "$end\n";
}

static uint64_t SignalDepth(std::string_view sig_name) {
  uint64_t depth = 1;
  for (char c : sig_name) {
    if (c == '.') ++depth;
  }
  return depth;
}

static std::string_view StripTopScope(std::string_view scope,
                                      std::string_view top_scope) {
  if (top_scope.empty()) return scope;
  if (scope == top_scope) return {};
  if (scope.size() > top_scope.size() + 1 &&
      scope.substr(0, top_scope.size()) == top_scope &&
      scope[top_scope.size()] == '.')
    return scope.substr(top_scope.size() + 1);
  return scope;
}

static bool OneScopeSelectsSignal(std::string_view sig_name,
                                  std::string_view scope, uint64_t level) {
  if (scope.empty()) return level == 0 || SignalDepth(sig_name) <= level;
  if (sig_name == scope) return true;
  if (sig_name.size() <= scope.size() + 1 ||
      sig_name.substr(0, scope.size()) != scope ||
      sig_name[scope.size()] != '.')
    return false;
  return level == 0 || SignalDepth(sig_name.substr(scope.size() + 1)) <= level;
}

static bool ScopeSelectsSignal(std::string_view sig_name,
                               const std::vector<std::string_view>& scopes,
                               uint64_t level, std::string_view top_scope) {
  for (std::string_view s : scopes) {
    if (OneScopeSelectsSignal(sig_name, StripTopScope(s, top_scope), level))
      return true;
  }
  return false;
}

void VcdWriter::DumpScopeSelectedValues(
    const std::vector<std::string_view>& names, uint64_t level) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  dump_started_ = true;
  NarrowSelectionToListed();
  Out() << CheckpointKeyword(port_nodes_, "$dumpvars", "$dumpports") << "\n";
  for (auto& sig : signals_) {
    if (!ScopeSelectsSignal(sig.name, names, level, top_scope_)) continue;
    sig.dump_selected = true;
    WriteSignalChange(sig);
  }
  Out() << "$end\n";
}

void VcdWriter::DumpAllValues(uint64_t time) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  EnsureTimestamp(time);
  DumpAllValues();
}

void VcdWriter::DumpScopeSelectedValues(
    const std::vector<std::string_view>& names, uint64_t level, uint64_t time) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  EnsureTimestamp(time);
  DumpScopeSelectedValues(names, level);
}

void VcdWriter::DumpAll(uint64_t time) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  EnsureTimestamp(time);
  DumpAll();
}

void VcdWriter::DumpOff(uint64_t time) {
  if (!ofs_.is_open()) return;
  EnsureTimestamp(time);
  DumpOff();
}

void VcdWriter::DumpOn(uint64_t time) {
  if (!ofs_.is_open()) return;
  EnsureTimestamp(time);
  DumpOn();
}

void VcdWriter::DumpAll() {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  Out() << CheckpointKeyword(port_nodes_, "$dumpall", "$dumpportsall") << "\n";
  for (auto& sig : signals_) {
    if (!DumpsObject(sig)) continue;
    WriteSignalChange(sig);
  }
  Out() << "$end\n";
}

void VcdWriter::DumpOff() {
  if (!ofs_.is_open()) return;
  Out() << CheckpointKeyword(port_nodes_, "$dumpoff", "$dumpportsoff") << "\n";
  for (auto& sig : signals_) {
    if (!DumpsObject(sig)) continue;
    WriteSignalAllX(sig);
  }
  Out() << "$end\n";
  enabled_ = false;
}

void VcdWriter::DumpOn() {
  if (!ofs_.is_open()) return;
  enabled_ = true;
  Out() << CheckpointKeyword(port_nodes_, "$dumpon", "$dumpportson") << "\n";
  for (auto& sig : signals_) {
    if (!DumpsObject(sig)) continue;
    WriteSignalChange(sig);
  }
  Out() << "$end\n";
}

void VcdWriter::Flush() {
  FlushDeclarations();
  if (!ofs_.is_open()) return;
  ofs_.flush();
}

void VcdWriter::WriteVcdClose(uint64_t final_time) {
  FlushDeclarations();
  if (!ofs_.is_open() || !extended_) return;
  Out() << "$vcdclose #" << final_time << " $end\n";
}

void VcdWriter::SchedulePortDumpStart(std::vector<std::string> scopes,
                                      uint64_t time) {
  port_start_pending_ = true;
  port_start_time_ = time;
  if (!port_start_scheduled_) {
    port_start_scheduled_ = true;
    port_scopes_ = std::move(scopes);
    port_selection_active_ = !port_scopes_.empty();
    return;
  }
  if (scopes.empty() || !port_selection_active_) {
    port_scopes_.clear();
    port_selection_active_ = false;
    return;
  }
  for (auto& s : scopes) port_scopes_.push_back(std::move(s));
}

void VcdWriter::EmitPendingPortStartCheckpoint() {
  port_start_pending_ = false;
  if (port_scopes_.empty()) {
    DumpAllValues(port_start_time_);
    return;
  }
  if (!ofs_.is_open() || !enabled_ || AtSizeLimit()) return;
  EnsureTimestamp(port_start_time_);
  std::vector<std::string_view> names(port_scopes_.begin(), port_scopes_.end());
  DumpScopeSelectedValues(names, 1);
}

void VcdWriter::DumpChangedValues(uint64_t) {
  FlushDeclarations();
  if (port_start_pending_) {
    EmitPendingPortStartCheckpoint();
    return;
  }
  if (!ofs_.is_open() || !enabled_ || !dump_started_) return;
  if (AtSizeLimit()) return;
  std::vector<std::string_view> selected(port_scopes_.begin(),
                                         port_scopes_.end());
  for (auto& sig : signals_) {
    if (!sig.var) continue;
    if (!DumpsObject(sig)) continue;
    if (port_selection_active_ &&
        !ScopeSelectsSignal(sig.name, selected, 1, top_scope_)) {
      continue;
    }
    if (!HasValueChanged(sig)) continue;
    WriteSignalChange(sig);
  }
}

}  // namespace delta
