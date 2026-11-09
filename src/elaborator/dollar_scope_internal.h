#pragma once

#include <deque>
#include <set>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/dollar_scope.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

struct SpecArg {
  std::string_view name;
  const Expr* value = nullptr;
  const DataType* type = nullptr;
};

struct Specialization {
  std::vector<SpecArg> args;
  const DollarScope* where = nullptr;
};

struct FoundClass {
  const ClassDecl* cls = nullptr;
  Specialization spec;
  const DollarScope* home = nullptr;
};

struct ClassRef {
  std::string_view scope;
  std::string_view name;
  const std::vector<DataType>& args;
};

struct ClassQuery {
  ClassQuery(const DollarParams& params, std::deque<DollarScope>& built)
      : params(params), built(built) {}

  const DollarParams& params;
  std::deque<DollarScope>& built;
  std::set<std::pair<const void*, const DollarScope*>> following;
  std::deque<DataType> made;
};

std::vector<SpecArg> ArgsOfTypes(const std::vector<DataType>& types);

FoundClass ClassInChain(std::string_view name, const DollarScope* from,
                        ClassQuery& query, int depth);

FoundClass ClassOfPrefix(const Expr* prefix, const DollarScope& scope,
                         ClassQuery& query, int depth);

FoundClass ClassOfRef(const ClassRef& ref, const DollarScope& from,
                      ClassQuery& query, int depth);

const DollarScope* MembersOf(const FoundClass& found, ClassQuery& query,
                             int depth);

const DollarScope* NamedPackageScope(std::string_view name, ClassQuery& query,
                                     int depth);

const DollarScope& PackageScope(const PackageDecl* pkg, ClassQuery& query,
                                int depth);

const DollarScope& UnitScope(ClassQuery& query, int depth);

const DollarScope& DesignScope(const ModuleDecl* decl, const DollarScope& outer,
                               ClassQuery& query, int depth);

void NoteItemNamesAt(const std::vector<ModuleItem*>& items,
                     const InstanceParams* instance, ClassQuery& query,
                     int depth, DollarScope& scope);

}  // namespace delta
