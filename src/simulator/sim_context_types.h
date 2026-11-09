#pragma once

#include <cstdint>
#include <cstdio>
#include <deque>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/assoc_index.h"
#include "simulator/class_object.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace delta {
struct Expr;
struct ModuleItem;
struct Process;

struct FileIoError {
  int32_t code = 0;
  std::string msg;
};

struct EnumMemberInfo {
  std::string_view name;
  uint64_t value = 0;
  uint64_t xz = 0;
};

struct ModportExpressionPort {
  Expr* expr = nullptr;
  std::string instance_prefix;
};

struct GenBlockSubroutineScope {
  std::string inst_prefix;
  std::vector<std::string> gen_prefixes;
  std::vector<std::pair<std::string_view, int64_t>> consts;
};

inline std::string ClassInlineEnumKey(std::string_view cls,
                                      std::string_view prop) {
  return std::string(cls) + "::$" + std::string(prop);
}

struct EnumTypeInfo {
  std::string_view type_name;
  std::vector<EnumMemberInfo> members;
  uint32_t width = 32;
  bool is_4state = false;
  bool is_signed = false;
};

struct StructTypeInfo;

struct StructFieldInfo {
  std::string_view name;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind type_kind = DataTypeKind::kLogic;
  bool is_signed = false;
  bool is_rand = false;
  bool is_randc = false;
  bool is_dynamic = false;
  uint32_t dyn_elem_width = 0;
  int32_t dyn_max_size = -1;
  const StructTypeInfo* nested = nullptr;
  std::string_view type_name = {};
  uint32_t elem_count = 0;
  int64_t elem_left = 0;
  int64_t elem_right = 0;
  const std::vector<Expr*>* unpacked_dims = nullptr;
  const Expr* default_expr = nullptr;
  int64_t packed_left = 0;
  int64_t packed_right = 0;
  uint32_t packed_elem_width = 0;
  std::optional<PackedRange> decl_range = std::nullopt;
  const std::vector<std::pair<Expr*, Expr*>>* inner_packed_dims = nullptr;
};

struct StructTypeInfo {
  std::string_view type_name;
  std::vector<StructFieldInfo> fields;
  uint32_t total_width = 0;
  bool is_packed = false;
  bool is_union = false;
  bool is_soft = false;
};

const StructFieldInfo* FindStructField(const StructTypeInfo* info,
                                       std::string_view name);
bool ResolveStructFieldPath(const StructTypeInfo* info, std::string_view path,
                            uint32_t* bit_offset, uint32_t* width,
                            DataTypeKind* out_kind = nullptr);
const StructFieldInfo* ResolveStructField(const StructTypeInfo* info,
                                          std::string_view path,
                                          uint32_t* bit_offset);

struct ScopeVariableSet {
  std::string prefix;
  std::vector<std::string> names;
};

struct ElementDriveSource {
  const Expr* rhs = nullptr;
  uint32_t src_lo = 0;
  uint32_t width = 0;
  uint32_t rhs_width = 0;
};

struct ElementDrive {
  ElementDriveSource forced;
  ElementDriveSource assigned;

  bool Drives() const {
    return forced.rhs != nullptr || assigned.rhs != nullptr;
  }
};

struct FixedDimShape {
  uint32_t size = 0;
  int64_t lo = 0;
  bool descending = false;
};

struct QueueObject {
  std::vector<Logic4Vec> elements;
  std::vector<uint64_t> element_ids;
  uint32_t elem_width = 32;
  bool is_4state = true;
  bool is_signed = false;
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;
  int32_t max_size = -1;
  uint32_t generation = 0;
  bool holds_class_handles = false;
  bool holds_events = false;

  std::map<uint64_t, ElementDrive> element_drives;

  bool ElementIsDriven(size_t index) const {
    if (index >= element_ids.size()) return false;
    auto it = element_drives.find(element_ids[index]);
    return it != element_drives.end() && it->second.Drives();
  }

  uint64_t AllocateId() { return ++next_elem_id_; }

  void AssignFreshIds();

  void AllocateIdsForAppended();

  bool elements_are_queues = false;
  uint32_t nested_queue_levels = 0;
  uint32_t element_array_size = 0;
  int64_t element_array_lo = 0;
  bool element_array_descending = false;
  std::vector<FixedDimShape> element_inner_dims;
  std::map<uint64_t, QueueObject*> element_queues;
  uint64_t ElementQueueKeyAt(uint64_t pos) const {
    return element_ids.size() == elements.size() ? element_ids[pos] : pos;
  }
  int64_t index_lo = 0;
  bool index_descending = false;
  int64_t PositionOf(int64_t index) const {
    if (!index_descending) return index - index_lo;
    return index_lo + static_cast<int64_t>(elements.size()) - 1 - index;
  }

 private:
  uint64_t next_elem_id_ = 0;
};

struct QueueRefBinding {
  QueueObject* queue = nullptr;
  uint64_t element_id = 0;
  Variable* local_var = nullptr;
  std::string_view var_name;
};

struct AssocArrayObject;

struct AssocRefBinding {
  AssocArrayObject* assoc = nullptr;
  bool is_string_key = false;
  AssocIndex int_key;
  std::string str_key;
  Variable* local_var = nullptr;
  std::string_view var_name;
};

struct AssocArrayObject {
  std::map<AssocIndex, Logic4Vec> int_data;
  std::map<std::string, Logic4Vec> str_data;
  uint32_t elem_width = 32;
  uint32_t index_width = 32;
  bool is_string_key = false;
  bool is_wildcard = false;
  bool is_4state = false;
  bool is_signed = false;
  bool is_index_signed = true;
  bool has_default = false;
  Logic4Vec default_value;
  bool has_elem_init = false;
  Logic4Vec elem_init;
  std::string_view elem_class;
  std::string_view index_class;
  std::string_view index_type_name;
  std::map<AssocIndex, ElementDrive> int_drives;
  std::map<std::string, ElementDrive> str_drives;
  bool elements_are_queues = false;
  bool element_queue_handles = false;
  uint32_t nested_queue_levels = 0;
  uint32_t element_array_size = 0;
  int64_t element_array_lo = 0;
  bool element_array_descending = false;
  std::vector<FixedDimShape> element_inner_dims;
  std::map<AssocIndex, QueueObject*> int_element_queues;
  std::map<std::string, QueueObject*> str_element_queues;
  const AssocArrayObject* element_assoc = nullptr;
  std::map<AssocIndex, AssocArrayObject*> int_element_assocs;
  std::map<std::string, AssocArrayObject*> str_element_assocs;
  uint32_t Size() const;
};

struct ArrayInfo {
  uint32_t lo = 0;
  uint32_t size = 0;
  uint32_t elem_width = 32;
  bool is_descending = false;
  bool is_dynamic = false;
  bool is_queue = false;
  bool is_4state = true;
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;
  std::string_view elem_type_name = {};
  std::optional<bool> elem_is_signed = std::nullopt;
  std::optional<PackedRange> elem_range = std::nullopt;
  bool elem_type_is_unpacked_array = false;
  std::vector<uint32_t> dim_los = {};
  std::vector<uint32_t> dim_sizes = {};
  std::vector<bool> dim_descending = {};
  bool elements_are_queues = false;
};

struct StochasticQueueEntry {
  uint64_t job_id = 0;
  uint64_t inform_id = 0;
  uint64_t arrival_tick = 0;
};

struct StochasticQueue {
  int64_t q_type = 0;
  int64_t max_length = 0;
  uint64_t count = 0;
  std::deque<StochasticQueueEntry> entries = {};

  uint64_t max_count = 0;
  uint64_t arrivals = 0;
  uint64_t first_arrival_tick = 0;
  uint64_t last_arrival_tick = 0;
  uint64_t departures = 0;
  uint64_t total_wait = 0;
  uint64_t shortest_wait = 0;
};

struct TimeFormatSpec {
  int units_number = -9;
  int precision_number = 0;
  std::string suffix_string;
  int minimum_field_width = 20;
};

struct NetSpec {
  Strength charge_strength = Strength::kMedium;
  uint64_t decay_ticks = 0;
  bool decays = false;
  bool is_user_nettype = false;
  std::string_view resolve_func = {};
  bool is_signed = false;
};

struct AssocArraySpec {
  uint32_t index_width = 32;
  bool is_wildcard = false;
  bool is_4state = false;
  bool is_index_signed = true;
  std::string_view index_class = {};
  std::string_view index_type_name = {};
};

}  // namespace delta
