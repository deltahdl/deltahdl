#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "elaborator/const_eval_internal.h"

namespace delta {

namespace {

LocalNames g_outermost_names;
LocalNames* g_locals = &g_outermost_names;

}  // namespace

LocalNameFrame::LocalNameFrame() : prev_(g_locals) { g_locals = &locals_; }

LocalNameFrame::LocalNameFrame(std::string_view genvar) : prev_(g_locals) {
  locals_.declared = prev_->declared;
  locals_.declared.insert(genvar);
  g_locals = &locals_;
}

LocalNameFrame::~LocalNameFrame() { g_locals = prev_; }

void DeclareLocalName(std::string_view name) {
  g_locals->declared.insert(name);
}

bool DeclaresLocalName(std::string_view name) {
  return g_locals->declared.contains(name);
}

std::optional<double> ConstFuncRealLocal(std::string_view name) {
  auto it = g_locals->reals.find(name);
  if (it == g_locals->reals.end()) return std::nullopt;
  return it->second;
}

void SetConstFuncRealLocal(std::string_view name, double value) {
  g_locals->reals[name] = value;
}

void ClearConstFuncRealLocal(std::string_view name) {
  g_locals->reals.erase(name);
}

const std::string* ConstFuncStringLocal(std::string_view name) {
  auto it = g_locals->strings.find(name);
  return it == g_locals->strings.end() ? nullptr : &it->second;
}

void SetConstFuncStringLocal(std::string_view name, std::string chars) {
  g_locals->strings[name] = std::move(chars);
}

}  // namespace delta
