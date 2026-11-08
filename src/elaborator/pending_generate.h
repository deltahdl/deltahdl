#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/type_eval.h"

namespace delta {

struct Expr;
struct ModuleDecl;
struct ModuleItem;
struct RtlirModule;

struct PendingGenerate {
  ModuleItem* item;
  RtlirModule* mod;
  TypedefMap typedefs;
  ScopeMap cu_param_scope;
  std::unordered_map<std::string_view, const ModuleItem*> func_decls;
  PropertyRegistry property_registry;
  std::string config_inst_path;
  std::string library;
  std::unordered_map<std::string_view, std::string_view> interface_inst_types;
  std::vector<const ModuleDecl*> module_decl_path;
  std::unordered_map<std::string_view, std::vector<Expr*>> td_array_dims;
};

}  // namespace delta
