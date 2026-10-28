#include "elaborator/unit_hier_names_from_root.h"

#include <format>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The names the compilation-unit scope of `unit` declares: its items' own,
// the classes it declares, and the enumeration constants its types declare.
std::unordered_set<std::string_view> UnitDeclaredNames(
    const CompilationUnit& unit) {
  std::unordered_set<std::string_view> names;
  for (const ModuleItem* item : unit.cu_items) {
    names.insert(item->name);
    if (item->class_decl != nullptr) names.insert(item->class_decl->name);
    for (const DataType* type : {&item->data_type, &item->typedef_type}) {
      for (const EnumMember& member : type->enum_members)
        names.insert(member.name);
    }
  }
  return names;
}

}  // namespace

void ReportUnitHierNamesFromRoot(const CompilationUnit& unit,
                                 const RtlirDesign& design,
                                 ProvidedNameCache& provided_cache,
                                 DiagEngine& diag) {
  std::unordered_set<std::string_view> reached = UnitDeclaredNames(unit);
  for (const RtlirModule* top : design.top_modules) reached.insert(top->name);
  for (const Expr* head : UnitSubroutineHierHeads(unit)) {
    if (reached.contains(head->text) ||
        ImportsProvideName(&unit, provided_cache, unit.cu_items, head->text)) {
      continue;
    }
    diag.Error(head->range.start,
               std::format("hierarchical name '{}' in a compilation-unit task "
                           "or function is read from $root, where no "
                           "top-level instance '{}' stands",
                           head->text, head->text),
               Subclause("3.12.1"));
  }
}

}  // namespace delta
