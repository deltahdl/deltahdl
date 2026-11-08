#include "elaborator/unit_aggregate_params.h"

#include <string>
#include <string_view>
#include <utility>

#include "parser/ast_type.h"

namespace delta {

static UnitAggregateParams* g_unit_aggregate_params = nullptr;

static std::string_view g_unit_name_prefix;

static UnitAggregateParams& InstalledParams() {
  static UnitAggregateParams outside_elaboration;
  return g_unit_aggregate_params != nullptr ? *g_unit_aggregate_params
                                            : outside_elaboration;
}

UnitAggregateParamGuard::UnitAggregateParamGuard(UnitAggregateParams& params)
    : prev_(std::exchange(g_unit_aggregate_params, &params)) {}

UnitAggregateParamGuard::~UnitAggregateParamGuard() {
  g_unit_aggregate_params = prev_;
}

UnitNamePrefixGuard::UnitNamePrefixGuard(std::string_view prefix)
    : prev_(std::exchange(g_unit_name_prefix, prefix)) {}

UnitNamePrefixGuard::~UnitNamePrefixGuard() { g_unit_name_prefix = prev_; }

std::string_view CurrentUnitNamePrefix() { return g_unit_name_prefix; }

static std::string UnitKey(std::string_view scope, std::string_view name) {
  if (scope.empty()) return std::string(name);
  return std::string(scope) + "." + std::string(name);
}

static bool MayHoldAggregate(const UnitParamSource& source) {
  if (source.value == nullptr) return false;
  return !source.dims.empty() || source.type.kind == DataTypeKind::kNamed ||
         source.type.kind == DataTypeKind::kStruct ||
         source.type.kind == DataTypeKind::kUnion;
}

void RegisterUnitAggregateParam(const UnitParamSource& source) {
  if (!MayHoldAggregate(source)) return;
  InstalledParams()[UnitKey(source.scope, source.name)] = UnitAggregateParam{
      source.value, source.type, source.dims.empty() ? nullptr : &source.dims,
      source.values, source.scope};
}

const UnitAggregateParam* FindUnitAggregateParam(std::string_view key) {
  const UnitAggregateParams& params = InstalledParams();
  auto it = params.find(std::string(key));
  return it == params.end() ? nullptr : &it->second;
}

const UnitAggregateParam* FindUnitAggregateParamNamed(std::string_view name) {
  if (!g_unit_name_prefix.empty()) {
    if (const UnitAggregateParam* own =
            FindUnitAggregateParam(UnitKey(g_unit_name_prefix, name)))
      return own;
  }
  return FindUnitAggregateParam(name);
}

}  // namespace delta
