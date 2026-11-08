#pragma once

#include <cstddef>
#include <string_view>
#include <unordered_map>

namespace delta {

struct ArrayInfo;
struct AssocArrayObject;
struct DataType;
struct ModuleItem;
struct QueueObject;
struct Variable;

struct Scope {
  std::unordered_map<std::string_view, Variable*> vars;
  std::unordered_map<std::string_view, ArrayInfo*> arrays;
  std::unordered_map<std::string_view, QueueObject*> queues;
  std::unordered_map<std::string_view, AssocArrayObject*> assoc_arrays;
  std::string_view package;
  std::unordered_map<std::string_view, const DataType*> type_actuals;
  bool is_subroutine = false;
  std::unordered_map<std::string_view, std::string_view> class_types;
  std::unordered_map<std::string_view, ModuleItem*> lets;
  std::string_view stmt_frame;
};

struct FrameOwnerEntry {
  std::string_view owner;
  size_t gen_depth = 0;
};

}  // namespace delta
