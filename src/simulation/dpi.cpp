#include "simulation/dpi.h"

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

namespace delta {

// =============================================================================
// DpiContext
// =============================================================================

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

uint64_t DpiContext::Call(std::string_view sv_name,
                          const std::vector<uint64_t>& args) const {
  const auto* func = FindImport(sv_name);
  if (func == nullptr || !func->impl) return 0;
  return func->impl(args);
}

bool DpiContext::HasImport(std::string_view sv_name) const {
  return import_index_.count(sv_name) != 0;
}

bool DpiContext::HasExport(std::string_view sv_name) const {
  return export_index_.count(sv_name) != 0;
}

}  // namespace delta
