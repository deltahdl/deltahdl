#include "simulator/dpi.h"

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

namespace delta {

void DpiContext::RegisterImport(DpiFunction func) {
  import_index_[func.sv_name] = imports_.size();
  imports_.push_back(std::move(func));
}

void DpiContext::RegisterExport(DpiExport exp) {
  export_index_[exp.sv_name] = exports_.size();
  exports_.push_back(exp);
}

const DpiFunction* DpiContext::FindImport(std::string_view sv_name) const {
  auto it = import_index_.find(sv_name);
  if (it == import_index_.end()) return nullptr;
  return &imports_[it->second];
}

Logic4Word DpiContext::Call(std::string_view sv_name,
                            const std::vector<Logic4Word>& args) const {
  const auto* func = FindImport(sv_name);
  if (func == nullptr || !func->impl) return Logic4Word{};
  return func->impl(args);
}

Logic4Word DpiContext::CallWithArgs(std::string_view sv_name,
                                    std::vector<Logic4Word>& args) const {
  const auto* func = FindImport(sv_name);
  if (func == nullptr) return Logic4Word{};
  if (func->arg_impl) return func->arg_impl(args);
  // An import written with the reading form leaves `args` as it found them, so
  // a call site copying an output or an inout formal back reads the value it
  // supplied. That is the same value the actual already holds, so the copy-back
  // changes nothing and the call behaves as it did before this form existed.
  if (func->impl) return func->impl(args);
  return Logic4Word{};
}

bool DpiContext::HasImport(std::string_view sv_name) const {
  return import_index_.count(sv_name) != 0;
}

bool DpiContext::HasExport(std::string_view sv_name) const {
  return export_index_.count(sv_name) != 0;
}

}  // namespace delta
