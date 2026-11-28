#pragma once

#include <cstddef>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

struct RealTyped {
  bool found = false;
  DataTypeKind kind = DataTypeKind::kImplicit;
  const DataType* aggregate = nullptr;
  const ClassDecl* cls = nullptr;
  const ModuleDecl* scope = nullptr;
  size_t unpacked = 0;
  bool is_param = false;
  bool is_function = false;
};

using RealNameLookup = std::function<RealTyped(std::string_view)>;
using TypedefDimsMap = std::unordered_map<std::string_view, std::vector<Expr*>>;

struct RealUseScope {
  const CompilationUnit* unit;
  const TypedefMap& typedefs;
  const TypedefDimsMap& typedef_dims;
  const std::vector<ModuleItem*>& items;
  const std::vector<ClassDecl*>& classes;
  RealNameLookup outer;
  DiagEngine& diag;
};

RealTyped RealTypedOfDecl(const DataType& type, size_t unpacked,
                          const RealUseScope& scope);

void ReportRealUsesInItem(const ModuleItem* item, const RealUseScope& scope);

void ReportRealUsesInItems(const std::vector<ModuleItem*>& items,
                           const RealUseScope& scope);

void ReportRealUsesInClass(const ClassDecl* cls, const RealUseScope& scope);

}  // namespace delta
