#pragma once

#include <functional>
#include <vector>

namespace delta {

struct VpiObject;

// §38.4: what vpi_control() has been asked for. vpiStop, vpiFinish and vpiReset
// request a built-in task, which executes on return of the application routine
// that made the request: a calltf, compiletf or callback routine. Routines run
// one inside another, a routine's VPI call reaching a system task whose calltf
// is an application of its own, so the requests wait for the outermost to
// return.
struct VpiControlRequests {
  bool stop_requested = false;
  bool finish_requested = false;
  // The diagnostic message level the most recent vpiStop or vpiFinish request
  // carried, the one $stop or $finish takes (§20.2).
  int stop_diag_level = 0;
  int finish_diag_level = 0;
  // A vpiReset request and its three arguments, those $reset takes (D.8).
  bool reset_requested = false;
  int reset_stop_value = 0;
  int reset_reset_value = 0;
  int reset_diag_value = 0;
  // The scope vpiSetInteractiveScope most recently made the interactive scope.
  VpiObject* interactive_scope = nullptr;
  // How many application routines are running, one inside another.
  int routines_running = 0;
  // The tasks requested while one runs, executed once the outermost returns.
  std::vector<std::function<void()>> on_return;
};

}  // namespace delta
