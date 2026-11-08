#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "simulator/sim_context.h"

namespace delta {

void SimContext::RegisterInstanceBinding(std::string_view prefix,
                                         std::string_view library,
                                         std::string_view cell) {
  instance_bindings_[std::string(prefix)] =
      std::string(library) + "." + std::string(cell);
}

std::string_view SimContext::FindInstanceBinding(
    std::string_view prefix) const {
  auto it = instance_bindings_.find(std::string(prefix));
  return (it != instance_bindings_.end()) ? std::string_view(it->second)
                                          : std::string_view{};
}

void SimContext::SetDeferredBindingScope(std::optional<std::string> prefix) {
  deferred_binding_scope_ = std::move(prefix);
}

const std::optional<std::string>& SimContext::DeferredBindingScope() const {
  return deferred_binding_scope_;
}

void SimContext::SetMonitorCaller(std::shared_ptr<Process> caller) {
  monitor_caller_ = std::move(caller);
}

}  // namespace delta
