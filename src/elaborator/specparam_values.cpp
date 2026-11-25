#include "elaborator/specparam_values.h"

#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

void Record(RtlirModule& mod, std::string_view name, Expr* value,
            const DataType* type) {
  RtlirParamDecl& specparam = mod.specparams.emplace_back();
  specparam.name = name;
  specparam.default_value = value;
  specparam.decl_type = type;
}

}  // namespace

void RecordSpecparams(const std::vector<ModuleItem*>& items, RtlirModule& mod,
                      Arena& arena) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kSpecparam) {
      Record(mod, item->name, item->init_expr, &item->data_type);
    }
    for (const SpecifyItem* specify : item->specify_items) {
      if (specify->kind != SpecifyItemKind::kSpecparam) continue;
      auto* type = arena.Create<DataType>();
      type->packed_dim_left = specify->param_packed_left;
      type->packed_dim_right = specify->param_packed_right;
      Record(mod, specify->param_name, specify->param_value, type);
    }
  }
}

void ResolveSpecparams(RtlirModule& mod, ScopeMap scope,
                       const TypedefMap& typedefs) {
  for (RtlirParamDecl& specparam : mod.specparams) {
    const DataType& type = *specparam.decl_type;
    PopulateParamTypeInfo(specparam, type, typedefs, scope);
    specparam.is_resolved = false;
    ResolveConstantValue(specparam, specparam.default_value, type, scope);
    if (specparam.is_resolved) {
      BindDeclaredConstant(scope, specparam.name, specparam.resolved_value);
    }
  }
}

}  // namespace delta
