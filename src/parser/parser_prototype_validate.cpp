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

// A class's `extern` and `pure virtual` methods are read through the same head,
// and their method_prototype is the same function_prototype or task_prototype,
// so the same three things are reported. A `static` lifetime is left to
// ValidateClassMethod, which reports it on any class method under §8.6, a
// class method being automatic. A constructor's class_constructor_prototype,
// `function new`, writes no result type at all.
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
      item->return_type.kind == DataTypeKind::kImplicit) {
    diag.Error(item->loc,
               "a class function prototype writes its result type out, a data "
               "type or void",
               Subclause("A.1.9"));
  }
}

}  // namespace delta
