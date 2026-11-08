#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

struct RtlirAssocIndex {
  bool is_string = false;
  bool is_wildcard = false;
  bool is_signed = true;
  uint32_t width = 32;
  std::string_view class_name;
  std::string_view type_name;
};

struct RtlirFixedDim {
  uint32_t size = 0;
  int64_t lo = 0;
  bool descending = false;
};

struct RtlirElementShape {
  uint32_t nested_queue_levels = 0;
  uint32_t array_size = 0;
  int64_t array_lo = 0;
  bool array_descending = false;
  std::vector<RtlirFixedDim> inner_array_dims;
  std::optional<RtlirAssocIndex> assoc_index;
  bool type_is_unpacked_array = false;
};

}  // namespace delta
