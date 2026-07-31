// The run-time state behind IEEE 1800-2023 §33.7, "Displaying library binding
// information": which library and cell each module instance of the design was
// bound to, and which instance a piece of textual output belongs to. It is
// written during lowering, once per instance, and read back by the %l / %L
// format specifier when a command produces output.
//
// It is split out of sim_context.cpp as a cohesive unit of its own, the way the
// file-I/O and class-collection state already are, so no one file carries the
// whole of the context's implementation.

#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "simulator/sim_context.h"

namespace delta {

void SimContext::RegisterInstanceBinding(std::string_view prefix,
                                         std::string_view library,
                                         std::string_view cell) {
  // §33.7: store the binding already joined as "library.cell" so the display
  // path can hand it straight back without re-formatting on every %l.
  instance_bindings_[std::string(prefix)] =
      std::string(library) + "." + std::string(cell);
}

std::string_view SimContext::FindInstanceBinding(
    std::string_view prefix) const {
  auto it = instance_bindings_.find(std::string(prefix));
  return (it != instance_bindings_.end()) ? std::string_view(it->second)
                                          : std::string_view{};
}

// §33.7: the binding the specifier reports belongs to the instance containing
// the output command. For a command that produces its text where it is written,
// that instance is the one named by the running process's prefix. For one whose
// text is produced later -- after the process that issued it has run to
// completion -- the running process is no longer the right answer: a process is
// installed on the context each time one resumes and the installation is
// cleared only when the run ends, so a deferred output would read back the
// process that happened to resume last. Such a command records its own call
// site before deferring, and this holds that record for the span of the output.
//
// Absence is carried by the optional rather than by an empty string, because an
// empty prefix is itself a value: it names the top instance.
void SimContext::SetDeferredBindingScope(std::optional<std::string> prefix) {
  deferred_binding_scope_ = std::move(prefix);
}

const std::optional<std::string>& SimContext::DeferredBindingScope() const {
  return deferred_binding_scope_;
}

// §33.7: a monitored display list outlives the call that installed it and is
// produced again on every change of a watched value, each time from outside the
// process that wrote it. The instance the list belongs to is therefore recorded
// once, when the list becomes the active one, and read back on every redisplay;
// installing a new list replaces the record along with the list.
void SimContext::SetMonitorBindingScope(std::string prefix) {
  monitor_binding_scope_ = std::move(prefix);
}

std::string_view SimContext::MonitorBindingScope() const {
  return monitor_binding_scope_;
}

}  // namespace delta
