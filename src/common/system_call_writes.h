#pragma once

#include <algorithm>
#include <cstddef>
#include <limits>
#include <string_view>

namespace delta {

inline constexpr std::string_view kPlaSystemTasks[] = {
    "$async$and$array",  "$async$nand$array", "$async$or$array",
    "$async$nor$array",  "$sync$and$array",   "$sync$nand$array",
    "$sync$or$array",    "$sync$nor$array",   "$async$and$plane",
    "$async$nand$plane", "$async$or$plane",   "$async$nor$plane",
    "$sync$and$plane",   "$sync$nand$plane",  "$sync$or$plane",
    "$sync$nor$plane"};

inline bool IsPlaSystemTask(std::string_view callee) {
  return std::ranges::any_of(kPlaSystemTasks, [callee](std::string_view task) {
    return task == callee;
  });
}

struct WrittenArguments {
  std::string_view callee;
  size_t first;
  size_t last;
};

inline constexpr size_t kThroughTheLastArgument =
    std::numeric_limits<size_t>::max();

inline constexpr WrittenArguments kSystemCallWrittenArguments[] = {
    {"$swrite", 0, 0},
    {"$swriteb", 0, 0},
    {"$swriteh", 0, 0},
    {"$swriteo", 0, 0},
    {"$sformat", 0, 0},
    {"$fgets", 0, 0},
    {"$fscanf", 2, kThroughTheLastArgument},
    {"$sscanf", 2, kThroughTheLastArgument},
    {"$fread", 0, 0},
    {"$ferror", 1, 1},
    {"$readmemb", 1, 1},
    {"$readmemh", 1, 1},
    {"$value$plusargs", 1, 1},
    {"$cast", 0, 0},
    {"$random", 0, 0},
    {"$dist_uniform", 0, 0},
    {"$dist_normal", 0, 0},
    {"$dist_exponential", 0, 0},
    {"$dist_poisson", 0, 0},
    {"$dist_chi_square", 0, 0},
    {"$dist_t", 0, 0},
    {"$dist_erlang", 0, 0},
    {"$q_initialize", 3, 3},
    {"$q_add", 3, 3},
    {"$q_remove", 1, 3},
    {"$q_full", 1, 1},
    {"$q_exam", 2, 3},
    {"$sreadmemb", 0, 0},
    {"$sreadmemh", 0, 0},
    {"$countdrivers", 1, 5},
};

inline bool SystemCallWritesArgument(std::string_view callee, size_t index) {
  if (IsPlaSystemTask(callee)) return index == 2;
  return std::ranges::any_of(kSystemCallWrittenArguments,
                             [callee, index](const WrittenArguments& written) {
                               return written.callee == callee &&
                                      written.first <= index &&
                                      index <= written.last;
                             });
}

}  // namespace delta
