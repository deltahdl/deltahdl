#pragma once

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>

#include "common/types.h"

namespace delta {

struct Expr;
struct Process;
struct Variable;

struct FileMonitor {
  const Expr* call = nullptr;
  std::string task_name;
  uint32_t descriptor = 0;
  std::shared_ptr<Process> caller;
  std::string scope;
  bool cancelled = false;
  bool one_shot = false;
  bool write_pending = false;
  std::unordered_map<Variable*, Logic4Vec> last_values;
};

}  // namespace delta
