#pragma once

#include <cstdint>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

// --- VCD waveform output (IEEE 1800-2023 section 21) ---

class VcdWriter {
 public:
  VcdWriter(std::string filename, std::string timescale);
  ~VcdWriter();

  VcdWriter(const VcdWriter&) = delete;
  VcdWriter& operator=(const VcdWriter&) = delete;

  void add_signal(std::string_view scope, std::string_view name,
                  uint32_t width);
  void write_header();
  void write_timestamp(SimTime time);
  void write_value_change(uint32_t signal_id, const Logic4Vec& value);
  void close();

 private:
  struct SignalEntry {
    std::string scope;
    std::string name;
    uint32_t width = 0;
    uint32_t id = 0;
  };

  static std::string make_id_string(uint32_t id);
  void write_initial_values();
  void write_scope_hierarchy();
  void write_signal_defs(const std::string& scope);
  void write_scalar_change(const Logic4Vec& value, const std::string& id_str);
  void write_vector_change(const Logic4Vec& value, uint32_t width,
                           const std::string& id_str);

  std::string filename_;
  std::string timescale_;
  std::ofstream file_;
  std::vector<SignalEntry> signals_;
  uint32_t next_id_ = 0;
  bool header_written_ = false;
};

}  // namespace delta
