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
  void DumpChangedValues(uint64_t prev_time);

  void SetEnabled(bool enabled) { enabled_ = enabled; }
  bool IsEnabled() const { return enabled_; }

 private:
  void WriteScalarChange(const VcdSignal& sig);
  void WriteVectorChange(const VcdSignal& sig);
  void WriteSignalChange(const VcdSignal& sig);

  std::ofstream ofs_;
  std::vector<VcdSignal> signals_;
  char next_ident_ = '!';
  bool enabled_ = true;
  uint64_t last_time_ = 0;
  bool header_written_ = false;
};

}
