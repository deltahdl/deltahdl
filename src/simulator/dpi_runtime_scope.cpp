// §H.9.3: the scope-name registry the svGetScopeFromName and svGetNameFromScope
// entry points consult, and the scope stack the context import frames of a
// DpiRuntime push, whose entries are the registry's handles.
#include <cstdint>
#include <functional>
#include <list>
#include <map>
#include <string>
#include <string_view>
#include <utility>

#include "simulator/dpi_runtime.h"

namespace delta {

namespace {
// §H.9.3 scope-name registry storage. std::list keeps element addresses stable
// as scopes are added, so a handle handed to C code stays valid for the life of
// the simulation. The by-name index drives svGetScopeFromName().
std::list<DpiScope>& DpiScopeRegistryStorage() {
  static std::list<DpiScope> storage;
  return storage;
}
std::map<std::string, DpiScope*, std::less<>>& DpiScopeRegistryByName() {
  static std::map<std::string, DpiScope*, std::less<>> by_name;
  return by_name;
}

DpiScope* RegisterScopeByName(std::string_view name) {
  auto& by_name = DpiScopeRegistryByName();
  auto it = by_name.find(name);
  if (it != by_name.end()) return it->second;
  DpiScope& scope = DpiScopeRegistryStorage().emplace_back();
  scope.name = std::string(name);
  by_name.emplace(scope.name, &scope);
  return &scope;
}
}  // namespace

const DpiScope* DpiRegisterScope(std::string_view name) {
  return RegisterScopeByName(name);
}

const DpiScope* DpiScopeFromName(std::string_view name) {
  auto& by_name = DpiScopeRegistryByName();
  auto it = by_name.find(name);
  return it == by_name.end() ? nullptr : it->second;
}

const char* DpiNameFromScope(const DpiScope* scope) {
  if (scope == nullptr) return "";
  // Only handles this registry produced map back to a name; an unregistered
  // pointer is not a recognized scope, so it yields an empty name rather than a
  // dereference of an unknown address.
  for (const DpiScope& s : DpiScopeRegistryStorage()) {
    if (&s == scope) return s.name.c_str();
  }
  return "";
}

namespace {
// The registry's own entry for a handle it produced, or nullptr for any other
// pointer, which is not a recognized scope.
DpiScope* RegisteredScope(const DpiScope* scope) {
  if (scope == nullptr) return nullptr;
  for (DpiScope& s : DpiScopeRegistryStorage()) {
    if (&s == scope) return &s;
  }
  return nullptr;
}
}  // namespace

void DpiSetScopeTimescale(const DpiScope* scope, int32_t time_unit,
                          int32_t time_precision) {
  DpiScope* registered = RegisteredScope(scope);
  if (registered == nullptr) return;
  registered->time_unit = time_unit;
  registered->time_precision = time_precision;
}

bool DpiScopeTimescale(const DpiScope* scope, int32_t* time_unit,
                       int32_t* time_precision) {
  const DpiScope* registered = RegisteredScope(scope);
  if (registered == nullptr || registered->time_unit == kDpiNoTimescale ||
      registered->time_precision == kDpiNoTimescale) {
    return false;
  }
  if (time_unit != nullptr) *time_unit = registered->time_unit;
  if (time_precision != nullptr) *time_precision = registered->time_precision;
  return true;
}

void DpiRuntime::PushScope(DpiScope scope) {
  // §H.9.3: a named scope is the instance scope its fully qualified name
  // resolves to, one handle per name for the life of the simulation, so the
  // frame's scope is the registry's handle and what the pushed scope knows of
  // its module completes a handle registered by name alone. A scope without a
  // name is nobody's instance and lives with its frame.
  if (scope.name.empty()) {
    unnamed_scopes_.push_back(std::move(scope));
    scope_stack_.push_back(&unnamed_scopes_.back());
  } else {
    DpiScope* registered = RegisterScopeByName(scope.name);
    if (registered->module_name.empty()) {
      registered->module_name = scope.module_name;
    }
    scope_stack_.push_back(registered);
  }
  current_scope_ = scope_stack_.back();
}

void DpiRuntime::PopScope() {
  if (scope_stack_.empty()) return;
  if (!unnamed_scopes_.empty() &&
      scope_stack_.back() == &unnamed_scopes_.back()) {
    unnamed_scopes_.pop_back();
  }
  scope_stack_.pop_back();
  current_scope_ = scope_stack_.empty() ? nullptr : scope_stack_.back();
}

const DpiScope* DpiRuntime::CurrentScope() const { return current_scope_; }

void DpiRuntime::SetScope(const DpiScope* scope) { current_scope_ = scope; }

const DpiScope* DpiRuntime::GetScope() const { return current_scope_; }

}  // namespace delta
