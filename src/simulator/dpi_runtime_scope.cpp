#include <algorithm>
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
  for (const DpiScope& s : DpiScopeRegistryStorage()) {
    if (&s == scope) return s.name.c_str();
  }
  return "";
}

namespace {
DpiScope* RegisteredScope(const DpiScope* scope) {
  if (scope == nullptr) return nullptr;
  for (DpiScope& s : DpiScopeRegistryStorage()) {
    if (&s == scope) return &s;
  }
  return nullptr;
}
}  // namespace

bool DpiScopeIsValid(const DpiScope* scope) {
  if (RegisteredScope(scope) != nullptr) return true;
  const DpiRuntime* runtime = DpiForeignRuntime();
  return scope != nullptr && runtime != nullptr && runtime->HoldsScope(scope);
}

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

bool DpiRuntime::HoldsScope(const DpiScope* scope) const {
  return std::find(scope_stack_.begin(), scope_stack_.end(), scope) !=
         scope_stack_.end();
}

}  // namespace delta
