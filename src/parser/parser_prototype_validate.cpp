#include "parser/parser_prototype_validate.h"

#include "common/diagnostic.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// The prototype is read through the head of a task or function declaration,
// which A.2.6 and A.2.7 let carry three things a prototype does not: a
// lifetime, an `interface_identifier .` or class_scope prefix on the name, and
// for a function an implicit result type, function_prototype taking a
// data_type_or_void. Each is reported at the prototype's `task` or `function`
// keyword.
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
      item->return_type.kind == DataTypeKind::kImplicit) {
    diag.Error(item->loc,
               "an extern function prototype writes its result type out, a "
               "data type or void",
               Subclause("A.1.6"));
  }
}

}  // namespace delta
