#include "elaborator/unit_param_values.h"

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/elaborator_items_params.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static UnitParamValues* g_unit_param_values = nullptr;

static std::string_view g_unit_name_prefix;

static UnitParamValues& InstalledParams() {
  static UnitParamValues outside_elaboration;
  return g_unit_param_values != nullptr ? *g_unit_param_values
                                        : outside_elaboration;
}

UnitParamValueGuard::UnitParamValueGuard(UnitParamValues& params)
    : prev_(std::exchange(g_unit_param_values, &params)) {}

UnitParamValueGuard::~UnitParamValueGuard() { g_unit_param_values = prev_; }

UnitNamePrefixGuard::UnitNamePrefixGuard(std::string_view prefix)
    : prev_(std::exchange(g_unit_name_prefix, prefix)) {}

UnitNamePrefixGuard::~UnitNamePrefixGuard() { g_unit_name_prefix = prev_; }

std::string_view CurrentUnitNamePrefix() { return g_unit_name_prefix; }

static std::string UnitKey(std::string_view scope, std::string_view name) {
  if (scope.empty()) return std::string(name);
  return std::string(scope) + "." + std::string(name);
}

static DataType RecordedType(const UnitParamSource& source) {
  if (!TakesItsTypeFromItsValue(source.type) || !HasRealOperand(source.value))
    return source.type;
  DataType real;
  real.kind = DataTypeKind::kReal;
  return real;
}

static bool MayHoldMoreThanAnInteger(const DataType& type,
                                     const std::vector<Expr*>& dims) {
  switch (type.kind) {
    case DataTypeKind::kNamed:
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kString:
      return true;
    default:
      return !dims.empty();
  }
}

void RegisterUnitParamValue(const UnitParamSource& source) {
  DataType type = RecordedType(source);
  if (!MayHoldMoreThanAnInteger(type, source.dims)) return;
  InstalledParams().declared[UnitKey(source.scope, source.name)] =
      UnitParamValue{source.value, std::move(type),
                     source.dims.empty() ? nullptr : &source.dims,
                     source.values, source.scope};
}

void RecordUnitParamImport(std::string_view importer, const ImportItem& item) {
  InstalledParams().imports[std::string(importer)].push_back(
      UnitParamImport{item.package_name, item.item_name, item.is_wildcard});
}

std::vector<std::string_view> UnitParamNamesImported(const ImportItem& item) {
  std::vector<std::string_view> names;
  const std::string kPrefix = UnitKey(item.package_name, {});
  for (const auto& entry : InstalledParams().declared) {
    std::string_view key = entry.first;
    if (!key.starts_with(kPrefix)) continue;
    std::string_view name = key.substr(kPrefix.size());
    if (item.is_wildcard || name == item.item_name) names.push_back(name);
  }
  return names;
}

const UnitParamValue* FindUnitParamValue(std::string_view key) {
  const auto& declared = InstalledParams().declared;
  auto it = declared.find(std::string(key));
  return it == declared.end() ? nullptr : &it->second;
}

const UnitParamValue* FindUnitParamValueImported(const UnitParamImport& imp,
                                                 std::string_view name) {
  if (!imp.is_wildcard && imp.item_name != name) return nullptr;
  return FindUnitParamValue(UnitKey(imp.package_name, name));
}

static const UnitParamValue* FindUnitParamValueVisibleIn(
    std::string_view scope, std::string_view name) {
  if (const UnitParamValue* declared = FindUnitParamValue(UnitKey(scope, name)))
    return declared;
  const auto& imports = InstalledParams().imports;
  auto it = imports.find(std::string(scope));
  if (it == imports.end()) return nullptr;
  for (const UnitParamImport& imp : it->second) {
    if (const UnitParamValue* found = FindUnitParamValueImported(imp, name))
      return found;
  }
  return nullptr;
}

const UnitParamValue* FindUnitParamValueOwn(std::string_view name) {
  if (g_unit_name_prefix.empty()) return nullptr;
  return FindUnitParamValueVisibleIn(g_unit_name_prefix, name);
}

const UnitParamValue* FindUnitParamValueNamed(std::string_view name) {
  if (const UnitParamValue* own = FindUnitParamValueOwn(name)) return own;
  return FindUnitParamValueVisibleIn({}, name);
}

}  // namespace delta
