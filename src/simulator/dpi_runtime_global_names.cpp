#include <cstdint>
#include <string_view>
#include <unordered_set>

#include "simulator/dpi_runtime.h"

namespace delta {

std::string_view DpiGlobalName(const DpiRtFunction& func) {
  return func.c_name.empty() ? func.sv_name : func.c_name;
}

std::string_view DpiGlobalName(const DpiRtExport& exp) {
  return exp.c_name.empty() ? exp.sv_name : exp.c_name;
}

const DpiRtFunction* DpiRuntime::FindImportByGlobalName(
    std::string_view global_name) const {
  auto it = import_global_index_.find(global_name);
  if (it == import_global_index_.end()) return nullptr;
  return &imports_[it->second];
}

const DpiRtExport* DpiRuntime::FindExportByGlobalName(
    std::string_view global_name) const {
  auto it = export_global_index_.find(global_name);
  if (it == export_global_index_.end()) return nullptr;
  return &exports_[it->second];
}

bool DpiRuntime::HasGlobalName(std::string_view global_name) const {
  return import_global_index_.count(global_name) != 0 ||
         export_global_index_.count(global_name) != 0;
}

uint32_t DpiRuntime::GlobalNameCount() const {
  // §35.4: one name space holds both kinds of declaration, so a linkage name an
  // import and an export both resolve to is one symbol and is counted once.
  std::unordered_set<std::string_view> names;
  for (const auto& entry : import_global_index_) names.insert(entry.first);
  for (const auto& entry : export_global_index_) names.insert(entry.first);
  return static_cast<uint32_t>(names.size());
}

}  // namespace delta
