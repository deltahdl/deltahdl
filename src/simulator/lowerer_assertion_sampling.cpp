#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

void Lowerer::EnrollInterfaceMembers(std::string_view name,
                                     const std::string& scope_prefix) {
  auto dot = name.rfind('.');
  if (dot == std::string_view::npos) return;
  std::string_view member = name.substr(dot + 1);
  ctx_.SetLoweringInstancePrefix("");
  for (const std::string& prefix : interface_instance_prefixes_) {
    if (auto* var = ctx_.FindVariable(prefix + std::string(member))) {
      ctx_.AssertionSamples().Register(var, ctx_.GetArena());
    }
  }
  ctx_.SetLoweringInstancePrefix(scope_prefix);
}

namespace {

void AppendLeafElements(const std::string& prefix,
                        const std::vector<uint32_t>& los,
                        const std::vector<uint32_t>& sizes, size_t dim,
                        std::vector<std::string>& out) {
  if (dim == los.size()) {
    out.push_back(prefix);
    return;
  }
  for (uint32_t i = 0; i < sizes[dim]; ++i) {
    AppendLeafElements(prefix + "[" + std::to_string(los[dim] + i) + "]", los,
                       sizes, dim + 1, out);
  }
}

}  // namespace

void Lowerer::EnrollArrayElements(const std::string& name) {
  const ArrayInfo* info = ctx_.FindArrayInfo(name);
  if (info == nullptr || info->is_dynamic || info->is_queue) return;
  std::vector<std::string> elements;
  if (info->dim_sizes.empty()) {
    AppendLeafElements(name, {info->lo}, {info->size}, 0, elements);
  } else {
    AppendLeafElements(name, info->dim_los, info->dim_sizes, 0, elements);
  }
  for (const std::string& element : elements) {
    if (auto* var = ctx_.FindVariable(element)) {
      ctx_.AssertionSamples().Register(var, ctx_.GetArena());
    }
  }
}

void Lowerer::RegisterDesignAssertionSampling() {
  for (const auto& scope : assertion_sample_scopes_) {
    ctx_.SetLoweringInstancePrefix(scope.inst_prefix);
    for (const auto& name : scope.names) {
      if (auto* var = ctx_.FindVariable(name)) {
        ctx_.AssertionSamples().Register(var, ctx_.GetArena());
      } else {
        EnrollInterfaceMembers(name, scope.inst_prefix);
      }
      EnrollArrayElements(name);
      if (auto* queue = ctx_.FindQueue(name)) {
        ctx_.AssertionSamples().RegisterQueue(queue, ctx_.GetArena());
      }
    }
  }
  ctx_.SetLoweringInstancePrefix("");
}

}  // namespace delta
