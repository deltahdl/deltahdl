#include "parser/parser_prototype_validate.h"

#include "common/diagnostic.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

bool IsImplicitResultType(const DataType& result) {
  return result.kind == DataTypeKind::kImplicit &&
         result.type_ref_expr == nullptr;
}

void ValidateExternTfPrototype(DiagEngine& diag, const ModuleItem* item) {
  if (item->is_automatic || item->is_static) {
    diag.Error(item->loc, "a task or function prototype takes no lifetime",
               Subclause("A.1.6"));
  }
  if (!item->method_class.empty()) {
    diag.Error(item->loc,
               "a task or function prototype names its task or function with "
               "an identifier alone",
               Subclause("A.1.6"));
  }
  if (item->kind == ModuleItemKind::kFunctionDecl &&
      IsImplicitResultType(item->return_type)) {
    diag.Error(item->loc,
               "an extern function prototype writes its result type out, a "
               "data type or void",
               Subclause("A.1.6"));
  }
}

void ValidateClassMethodPrototype(DiagEngine& diag, const ModuleItem* item) {
  if (item->is_automatic) {
    diag.Error(item->loc, "a class method prototype takes no lifetime",
               Subclause("A.1.9"));
  }
  if (!item->method_class.empty()) {
    diag.Error(item->loc,
               "a class method prototype names its method with an identifier "
               "alone",
               Subclause("A.1.9"));
  }
  if (item->kind == ModuleItemKind::kFunctionDecl && item->name != "new" &&
      IsImplicitResultType(item->return_type)) {
    diag.Error(item->loc,
               "a class function prototype writes its result type out, a data "
               "type or void",
               Subclause("A.1.9"));
  }
}

}  // namespace delta
