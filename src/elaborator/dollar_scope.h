#pragma once

#include <cstdint>
#include <deque>
#include <set>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct Expr;
struct InstanceParams;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;
struct Stmt;
struct DollarScope;

struct DollarClass {
  const ClassDecl* cls = nullptr;
  const DataType* alias = nullptr;
  const Expr* prefix = nullptr;
  const PackageDecl* package = nullptr;
  const DollarScope* where = nullptr;
};

struct DollarScope {
  const DollarScope* outer = nullptr;
  std::unordered_set<std::string_view> non_queues;
  std::unordered_set<std::string_view> others;
  std::unordered_set<std::string_view> dollar_params;
  std::unordered_set<std::string_view> overridden;
  std::unordered_set<std::string_view> takers;
  std::unordered_map<std::string_view, DollarClass> classes;
};

struct DollarParams {
  std::set<std::pair<std::string_view, std::string_view>> scoped;
  std::unordered_map<std::string_view, const PackageDecl*> packages;
  const CompilationUnit* unit = nullptr;
  mutable std::deque<DollarScope> cached;
  mutable std::unordered_map<const PackageDecl*, const DollarScope*>
      package_scopes;
  mutable const DollarScope* unit_scope = nullptr;
};

struct DollarClassStore {
  std::deque<DollarScope> scopes;
};

struct DollarTaker {
  const ModuleItem* decl = nullptr;
  const ModuleDecl* checker = nullptr;
  const PackageDecl* package = nullptr;
};

using DollarTakers = std::unordered_map<std::string_view, DollarTaker>;

struct DollarReport {
  const DollarTakers& dollar_takers;
  const DollarParams& params;
  DiagEngine& diag;
  std::set<std::tuple<uint32_t, uint32_t, uint32_t>> reported;
};

struct DollarScan {
  const DollarScope& scope;
  DollarReport& report;
};

enum class NameRole : uint8_t { kUnknown, kNonQueue, kOther, kDollarParam };

NameRole RoleOf(const DollarScope* scope, std::string_view name);

std::string_view DollarParamNamed(const Expr* e, const DollarScope& scope,
                                  const DollarParams& params);

std::string_view DollarParamNamed(const Expr* e, const DollarScan& scan);

std::string_view DefaultDollarParam(const Expr* value,
                                    std::string_view taker_name,
                                    const DollarTaker& taker,
                                    const DollarScan& scan);

void NoteDeclaredName(std::string_view name, const DataType& type,
                      const std::vector<Expr*>& dims, DollarScope& scope);

void NoteInstanceParam(std::string_view name, const InstanceParams& instance,
                       DollarScope& scope);

bool NamesNonQueue(const DollarScope* scope, std::string_view name);

void NoteItemNames(const std::vector<ModuleItem*>& items,
                   const DollarParams& params, const InstanceParams* instance,
                   DollarScope& scope);

void NoteUnitNames(const CompilationUnit& unit, const DollarParams& params,
                   DollarScope& scope);

void NoteClassNames(const ClassDecl* cls, const DollarParams& params,
                    DollarClassStore& store, DollarScope& scope);

DollarParams UnitDollarParams(const CompilationUnit& unit);

void NoteLocalNames(const Stmt* s, DollarScope& scope);

void AddDollarTakers(const std::vector<ModuleItem*>& items,
                     const PackageDecl* package, DollarTakers& takers);

DollarTakers UnitDollarTakers(const CompilationUnit& unit);

}  // namespace delta
