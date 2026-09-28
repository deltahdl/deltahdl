#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

namespace delta {

// §7.8 (printed pages 162-163): the index type an associative dimension
// declares, as RtlirVariable records its first dimension's: a string, a
// wildcard, or an integral type of `width` bits, signed or not, where
// `class_name` names a class index and `type_name` a typedef index.
struct RtlirAssocIndex {
  bool is_string = false;
  bool is_wildcard = false;
  bool is_signed = true;
  uint32_t width = 32;
  std::string_view class_name;
  std::string_view type_name;
};

// §7.4 with §7.5, §7.8 and §7.10 (printed pages 153, 157, 162 and 169): what
// each element of a queue, dynamic array, associative array or fixed-size
// array is where it is an array itself, beyond RtlirVariable's
// elements_are_queues.
struct RtlirElementShape {
  // How many levels of queues each element's queue holds below it, one for
  // `int arr[2][][]`, whose arr[0][0] is a queue too, and none for `int
  // qq[$][$]`.
  uint32_t nested_queue_levels = 0;
  // For a queue or dynamic array whose elements are fixed-size arrays, `int
  // q[$][3]`, the number of elements each holds, each element being kept as
  // a queue of exactly that many; 0 otherwise.
  uint32_t array_size = 0;
  // For an associative array whose element type is itself an associative
  // array, `int m[string][int]`, the index its elements have; empty for any
  // other variable.
  std::optional<RtlirAssocIndex> assoc_index;
};

}  // namespace delta
