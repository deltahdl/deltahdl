#pragma once

#include <functional>
#include <vector>

namespace delta {

struct VpiObject;

struct VpiControlRequests {
  bool stop_requested = false;
  bool finish_requested = false;
  int stop_diag_level = 0;
  int finish_diag_level = 0;
  VpiObject* interactive_scope = nullptr;
  int routines_running = 0;
  std::vector<std::function<void()>> on_return;
};

}  // namespace delta
