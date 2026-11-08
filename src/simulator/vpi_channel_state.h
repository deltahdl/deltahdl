#pragma once

#include <iosfwd>
#include <string>
#include <unordered_map>

#include "simulator/vpi_user.h"

namespace delta {

struct VpiChannelState {
  std::string output_channel_buffer;
  std::string output_channel_flushed;
  std::string log_file_buffer;
  std::string log_file_flushed;
  std::ostream* run_output = nullptr;
  bool flush_should_fail = false;

  std::unordered_map<std::string, PLI_UINT32> mcd_open_files;
  PLI_UINT32 mcd_allocated_channels = 0;
  bool mcd_open_should_fail = false;

  std::unordered_map<PLI_UINT32, std::string> mcd_channel_buffers;
  std::unordered_map<PLI_UINT32, std::string> mcd_channel_flushed;
  bool mcd_flush_should_fail = false;
  std::string empty_mcd_buffer;

  std::string mcd_name_buffer;
};

}  // namespace delta
