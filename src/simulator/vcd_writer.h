#pragma once

#include <cstdint>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct Variable;

struct VcdSignal {
  std::string_view name;
  uint32_t width = 1;
  Variable* var = nullptr;
  char ident = '!';
};

class VcdWriter {
 public:
  explicit VcdWriter(const std::string& filename);
  ~VcdWriter();

  VcdWriter(const VcdWriter&) = delete;
  VcdWriter& operator=(const VcdWriter&) = delete;

  bool IsOpen() const { return ofs_.is_open(); }

  void WriteHeader(std::string_view timescale);
  void BeginScope(std::string_view name);
  void EndScope();
  void RegisterSignal(std::string_view name, uint32_t width, Variable* var);
  void EndDefinitions();

  void WriteTimestamp(uint64_t time);
  void DumpAllValues();
  void DumpSelectedValues(const std::vector<std::string_view>& names);
  void DumpChangedValues(uint64_t prev_time);

  // Generate a checkpoint (§21.7.1.4): emit a $dumpall checkpoint recording the
  // current value of every selected variable.
  void DumpAll();

  // Suspend the dump (§21.7.1.3): emit a checkpoint that records every selected
  // variable as x and then stop recording further value changes.
  void DumpOff();
  // Resume the dump (§21.7.1.3): re-enable recording and emit a checkpoint of
  // each variable's current value.
  void DumpOn();

  void SetEnabled(bool enabled) { enabled_ = enabled; }
  bool IsEnabled() const { return enabled_; }

  // Read the dump file during simulation (§21.7.1.6): push any buffered output
  // out to the file so an application reading the file mid-simulation sees every
  // value change recorded so far. The dump state is untouched, so dumping
  // continues afterward exactly as before and no value changes are lost.
  void Flush();

  // Limit the dump file size (§21.7.1.5): once the file reaches limit_bytes the
  // dumper stops recording and inserts a comment noting the limit was reached.
  void SetSizeLimit(uint64_t limit_bytes) { size_limit_ = limit_bytes; }

 private:
  void WriteScalarChange(const VcdSignal& sig);
  void WriteVectorChange(const VcdSignal& sig);
  void WriteSignalChange(const VcdSignal& sig);
  void WriteSignalAllX(const VcdSignal& sig);
  // Returns true once the configured size limit has been reached, emitting the
  // limit comment exactly once when the threshold is first crossed.
  bool AtSizeLimit();

  std::ofstream ofs_;
  std::vector<VcdSignal> signals_;
  char next_ident_ = '!';
  bool enabled_ = true;
  uint64_t last_time_ = 0;
  bool header_written_ = false;
  uint64_t size_limit_ = 0;
  bool limit_reached_ = false;
};

}
