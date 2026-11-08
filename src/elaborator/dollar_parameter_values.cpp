#include "elaborator/dollar_parameter_values.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/dollar_contexts.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/net_data_type.h"
#include "elaborator/simple_bit_vector.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct ParamValue {
  std::string_view name;
  const Expr* value;
  const DataType* type;
  bool has_unpacked_dims;
};

struct DollarValueScan {
  const CompilationUnit* unit;
  const TypeShapeTables& tables;
  DiagEngine& diag;
};

void CheckParamValue(const ParamValue& param, const DollarValueScan& scan) {
  if (!ContainsDollar(param.value)) return;
  if (param.value->kind == ExprKind::kIdentifier && param.value->text == "$") {
    ValidateUnboundedParamType({param.name, param.type, param.has_unpacked_dims,
                                param.value->range.start},
                               scan.tables, scan.diag);
    return;
  }
  scan.diag.Error(param.value->range.start,
                  std::format("'$' may only be assigned to parameter '{}' as "
                              "a complete, self-contained expression",
                              param.name),
                  Subclause("6.20.7"));
}

bool IsValueParam(const ClassDecl& cls, size_t index) {
  return index < cls.params.size() &&
         cls.type_param_names.count(cls.params[index].first) == 0;
}

ParamValue PortParam(const ClassDecl& cls, size_t index, const Expr* value) {
  std::string_view name = cls.params[index].first;
  const DataType* type =
      index < cls.param_types.size() ? &cls.param_types[index] : nullptr;
  return {name, value, type, cls.param_port_unpacked_dims.count(name) != 0};
}

size_t PortParamIndex(const ClassDecl& cls, const DataType& value,
                      size_t position) {
  if (value.param_arg_name.empty()) return position;
  size_t index = 0;
  while (index < cls.params.size() &&
         cls.params[index].first != value.param_arg_name) {
    ++index;
  }
  return index;
}

void CheckSpecializationDollarValues(std::string_view class_name,
                                     const std::vector<DataType>& values,
                                     const DollarValueScan& scan) {
  if (values.empty()) return;
  const ClassDecl* cls = FindClassDecl(class_name, scan.unit);
  if (cls == nullptr) return;
  for (size_t i = 0; i < values.size(); ++i) {
    const DataType& value = values[i];
    const size_t kIndex = PortParamIndex(*cls, value, i);
    if (value.type_name.empty() && value.type_ref_expr != nullptr &&
        IsValueParam(*cls, kIndex)) {
      CheckParamValue(PortParam(*cls, kIndex, value.type_ref_expr), scan);
    }
  }
}

void CheckClassDollarValues(const ClassDecl& cls, const DollarValueScan& scan) {
  for (size_t i = 0; i < cls.params.size(); ++i) {
    if (IsValueParam(cls, i))
      CheckParamValue(PortParam(cls, i, cls.params[i].second), scan);
  }
  for (const ClassMember* m : cls.members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    if (m->is_param) {
      CheckParamValue(
          {m->name, m->init_expr, &m->data_type, !m->unpacked_dims.empty()},
          scan);
    } else {
      CheckSpecializationDollarValues(m->data_type.type_name,
                                      m->data_type.type_params, scan);
    }
  }
  CheckSpecializationDollarValues(cls.base_class, cls.base_class_type_params,
                                  scan);
}

void CheckVariableDollarValues(const std::vector<ModuleItem*>& items,
                               const DollarValueScan& scan);

void CheckGenerateDollarValues(const ModuleItem* item,
                               const DollarValueScan& scan) {
  for (; item != nullptr; item = item->gen_else) {
    CheckVariableDollarValues(item->gen_body, scan);
    for (const auto& case_item : item->gen_case_items)
      CheckVariableDollarValues(case_item.body, scan);
  }
}

void CheckVariableDollarValues(const std::vector<ModuleItem*>& items,
                               const DollarValueScan& scan) {
  for (const ModuleItem* item : items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kVarDecl) {
      CheckSpecializationDollarValues(item->data_type.type_name,
                                      item->data_type.type_params, scan);
    }
    CheckGenerateDollarValues(item, scan);
  }
}

}  // namespace

void CheckClassParamDollarValues(const CompilationUnit* unit,
                                 const TypeShapeTables& tables,
                                 DiagEngine& diag) {
  const DollarValueScan kScan{unit, tables, diag};
  for (const ClassDecl* cls : AllClassDecls(unit))
    CheckClassDollarValues(*cls, kScan);
  CheckVariableDollarValues(unit->cu_items, kScan);
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* decl : *group)
      CheckVariableDollarValues(decl->items, kScan);
  }
  for (const PackageDecl* pkg : unit->packages)
    CheckVariableDollarValues(pkg->items, kScan);
}

}  // namespace delta
