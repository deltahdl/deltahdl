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

// §21.3.2 (printed page 667): one $fmonitor task. It works as $monitor
// (§21.2.3) does, writing its list when it is called and again at the end of
// any time step in which one of its arguments changed, except that it writes
// to the file or files its descriptor selects -- and, where only one $monitor
// is active at a time, any number of $fmonitor tasks can be active together,
// so each call is a monitor of its own rather than a replacement of the last.
// An $fclose of its descriptor cancels it (§21.3.1). An $fstrobe is the same
// write made once, at the end of the step it was called in.
struct FileMonitor {
  const Expr* call = nullptr;
  // The task name as written, which picks the default radix of an
  // unformatted argument ($fmonitorb, $fmonitoro, $fmonitorh).
  std::string task_name;
  // The descriptor as the call evaluated it: a later change to the variable
  // that held it redirects nothing.
  uint32_t descriptor = 0;
  // A stand-in for the process that called the task, taken at the call and
  // reinstated for each write (deferred_caller.h), so the list reads the names
  // of the instance it was written in -- a class method's object and locals
  // among them -- and %m (§21.2.1.5) names that instance's scope; null for a
  // call made outside any process.
  std::shared_ptr<Process> caller;
  // That process's instance, for the binding %l reports (§33.7).
  std::string scope;
  bool cancelled = false;
  // An $fstrobe (§21.3.2): written once, at the end of the step it was called
  // in, with no argument watched.
  bool one_shot = false;
  bool write_pending = false;
  // The value each watched variable held when the list was last written, so
  // an assignment that leaves a value as it was writes nothing.
  std::unordered_map<Variable*, Logic4Vec> last_values;
};

}  // namespace delta
