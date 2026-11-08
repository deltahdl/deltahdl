#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

enum class ClassMemberKind : uint8_t {
  kProperty,
  kMethod,
  kConstraint,
  kTypedef,
  kClassDecl,
  kCovergroup,
};

struct ConstraintForeachRef {
  std::string_view array_name;
  int loop_var_count = 0;
  std::vector<std::string_view> loop_vars;
  std::vector<Expr*> body;
  SourceLoc loc;
};

struct ConstraintSolveBeforeEntry {
  std::string_view name;
  bool is_simple = true;
  std::vector<std::string_view> handles;
};

struct ConstraintSolveBeforeRef {
  std::vector<ConstraintSolveBeforeEntry> before;
  std::vector<ConstraintSolveBeforeEntry> after;
  SourceLoc loc;
};

struct ConstraintFunctionCallRef {
  std::string_view callee;
  SourceLoc loc;
};

struct ConstraintSoftVarRef {
  std::string_view name;
  SourceLoc loc;
};

struct ConstraintDistItem {
  Expr* value = nullptr;
  Expr* lo = nullptr;
  Expr* hi = nullptr;
  Expr* tolerance = nullptr;
  Expr* weight = nullptr;
  bool tolerance_relative = false;
  bool is_range = false;
  bool per_element = false;
  bool is_default = false;
};

struct ConstraintDistRef {
  Expr* target = nullptr;
  std::vector<ConstraintDistItem> items;
};

enum class ConstraintItemKind : uint8_t {
  kExpression,
  kUnique,
  kImplication,
  kIfElse,
  kForeach,
  kDisableSoft,
  kSolveBefore,
};

struct ConstraintItem {
  ConstraintItemKind kind = ConstraintItemKind::kExpression;
  bool soft = false;
  Expr* expr = nullptr;
  bool has_dist = false;
  std::vector<ConstraintDistItem> dist;
  std::vector<Expr*> exprs;
  std::vector<Expr*> after;
  std::vector<std::string_view> loop_vars;
  std::vector<ConstraintItem*> body;
  bool has_else = false;
  std::vector<ConstraintItem*> else_body;
};

struct ClassMember {
  ClassMemberKind kind = ClassMemberKind::kProperty;
  SourceLoc loc;
  std::vector<Attribute> attrs;

  bool is_static = false;
  bool is_virtual = false;
  bool is_local = false;
  bool is_protected = false;
  bool is_rand = false;
  bool is_randc = false;
  bool is_const = false;
  bool is_pure_virtual = false;
  bool extern_follows_qualifier = false;
  bool pure_apart_from_virtual = false;
  bool pure_follows_qualifier = false;
  bool random_follows_const = false;
  bool is_param = false;

  bool is_constraint_initial = false;
  bool is_constraint_extends = false;
  bool is_constraint_final = false;

  bool is_constraint_prototype = false;
  bool is_constraint_extern = false;

  std::vector<ConstraintForeachRef> constraint_foreach_refs;

  std::vector<ConstraintSolveBeforeRef> constraint_solve_before_refs;

  std::vector<ConstraintFunctionCallRef> constraint_function_call_refs;

  std::vector<ConstraintSoftVarRef> constraint_soft_refs;

  std::vector<Expr*> constraint_exprs;

  std::vector<ConstraintDistRef> constraint_dist_refs;

  std::vector<ConstraintSoftVarRef> constraint_disable_soft_refs;

  std::vector<Expr*> constraint_soft_exprs;

  std::vector<ConstraintDistRef> constraint_soft_dist_refs;

  std::vector<std::vector<Expr*>> constraint_unique_refs;

  std::vector<ConstraintItem*> constraint_items;
  bool constraint_items_parsed = false;

  DataType data_type;
  std::string_view name;
  std::vector<Expr*> unpacked_dims;
  Expr* init_expr = nullptr;

  ModuleItem* method = nullptr;
  ModuleItem* typedef_item = nullptr;

  ClassDecl* nested_class = nullptr;

  std::string_view covergroup_extends_base;

  CovergroupDecl* covergroup = nullptr;

  DataTypeKind type_param_restriction = DataTypeKind::kImplicit;
};

struct InterfaceRef {
  std::string_view name;
  std::vector<DataType> type_params;
  std::string_view scope;
};

struct ClassDecl {
  std::string_view name;
  SourceRange range;
  std::vector<Attribute> attrs;
  bool is_virtual = false;
  bool is_final = false;
  bool is_interface = false;
  std::string_view base_class;
  std::string_view base_class_scope;
  std::vector<DataType> base_class_type_params;
  std::vector<Expr*> extends_args;
  bool extends_has_default = false;
  std::vector<InterfaceRef> extends_interfaces;
  std::vector<InterfaceRef> implements_types;
  std::vector<ClassMember*> members;
  std::vector<std::pair<std::string_view, Expr*>> params;
  std::vector<DataType> param_types;
  std::unordered_map<std::string_view, std::vector<Expr*>>
      param_port_unpacked_dims;
  std::unordered_set<std::string_view> type_param_names;
  std::unordered_set<std::string_view> localparam_port_names;
  std::vector<SourceLoc> param_port_locs;
  std::unordered_map<std::string_view, DataTypeKind> type_param_restrictions;
};

}  // namespace delta
