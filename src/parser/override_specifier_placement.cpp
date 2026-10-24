#include "parser/override_specifier_placement.h"

#include "common/diagnostic.h"
#include "parser/ast_module.h"

namespace delta {

void ReportMisplacedOverrideSpecifiers(const ModuleItem& item,
                                       DiagEngine& diag) {
  if (!item.is_method_initial && !item.is_method_extends &&
      !item.is_method_final) {
    return;
  }
  if (item.kind == ModuleItemKind::kTaskDecl) {
    diag.Error(item.loc,
               "a task's dynamic_override_specifiers belong on a class method "
               "declaration, and an interface class takes none",
               Subclause("13.3"));
    return;
  }
  diag.Error(item.loc,
             "a function's dynamic_override_specifiers belong on a class "
             "method declaration, and an interface class takes none",
             Subclause("13.4"));
}

}  // namespace delta
