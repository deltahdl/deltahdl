#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/const_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

struct UnitAggregateParam {
  const Expr* value = nullptr;
  DataType type;
  const std::vector<Expr*>* dims = nullptr;
  ScopeMap scope;
  std::string_view prefix;
};

using UnitAggregateParams = std::unordered_map<std::string, UnitAggregateParam>;

class UnitAggregateParamGuard {
 public:
  explicit UnitAggregateParamGuard(UnitAggregateParams& params);
  ~UnitAggregateParamGuard();
  UnitAggregateParamGuard(const UnitAggregateParamGuard&) = delete;
  UnitAggregateParamGuard& operator=(const UnitAggregateParamGuard&) = delete;
  UnitAggregateParamGuard(UnitAggregateParamGuard&&) = delete;
  UnitAggregateParamGuard& operator=(UnitAggregateParamGuard&&) = delete;

 private:
  UnitAggregateParams* prev_;
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

void RegisterUnitAggregateParam(const UnitParamSource& source);

const UnitAggregateParam* FindUnitAggregateParam(std::string_view key);

const UnitAggregateParam* FindUnitAggregateParamNamed(std::string_view name);

}  // namespace delta
