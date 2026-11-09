#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/const_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;
struct ImportItem;

struct UnitParamValue {
  const Expr* value = nullptr;
  DataType type;
  const std::vector<Expr*>* dims = nullptr;
  ScopeMap scope;
  std::string_view prefix;
};

struct UnitParamImport {
  std::string_view package_name;
  std::string_view item_name;
  bool is_wildcard = false;
};

struct UnitParamValues {
  std::unordered_map<std::string, UnitParamValue> declared;
  std::unordered_map<std::string, std::vector<UnitParamImport>> imports;
};

class UnitParamValueGuard {
 public:
  explicit UnitParamValueGuard(UnitParamValues& params);
  ~UnitParamValueGuard();
  UnitParamValueGuard(const UnitParamValueGuard&) = delete;
  UnitParamValueGuard& operator=(const UnitParamValueGuard&) = delete;
  UnitParamValueGuard(UnitParamValueGuard&&) = delete;
  UnitParamValueGuard& operator=(UnitParamValueGuard&&) = delete;

 private:
  UnitParamValues* prev_;
};

class UnitNamePrefixGuard {
 public:
  explicit UnitNamePrefixGuard(std::string_view prefix);
  ~UnitNamePrefixGuard();
  UnitNamePrefixGuard(const UnitNamePrefixGuard&) = delete;
  UnitNamePrefixGuard& operator=(const UnitNamePrefixGuard&) = delete;
  UnitNamePrefixGuard(UnitNamePrefixGuard&&) = delete;
  UnitNamePrefixGuard& operator=(UnitNamePrefixGuard&&) = delete;

 private:
  std::string_view prev_;
};

std::string_view CurrentUnitNamePrefix();

struct UnitParamSource {
  std::string_view scope;
  std::string_view name;
  const Expr* value;
  const DataType& type;
  const std::vector<Expr*>& dims;
  const ScopeMap& values;
};

void RegisterUnitParamValue(const UnitParamSource& source);

void RecordUnitParamImport(std::string_view importer, const ImportItem& item);

std::vector<std::string_view> UnitParamNamesImported(const ImportItem& item);

const UnitParamValue* FindUnitParamValue(std::string_view key);

const UnitParamValue* FindUnitParamValueImported(const UnitParamImport& imp,
                                                 std::string_view name);

const UnitParamValue* FindUnitParamValueOwn(std::string_view name);

const UnitParamValue* FindUnitParamValueInTheCompilationUnit(
    std::string_view name);

}  // namespace delta
