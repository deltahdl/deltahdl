#include "elaborator/unit_scope_switch.h"

#include <cstddef>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/compilation_unit_set.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_type_facts.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"

namespace delta {

Elaborator::Elaborator(Arena& arena, DiagEngine& diag,
                       const std::vector<CompilationUnit*>& units)
    : ElaboratorClassRules(arena, diag, nullptr) {
  units_ = PoolCompilationUnits(units, arena);
  unit_ = units_.merged;
}

std::shared_ptr<UnitScopeTables> UnitScopeTables::Take(const Elaborator& e) {
  return std::make_shared<UnitScopeTables>(UnitScopeTables{
      e.typedefs_, e.cu_param_scope_, e.cu_scope_names_, e.class_names_,
      e.aggregate_typedef_names_, e.parameterized_class_names_,
      e.td_array_dims_, e.nettype_names_, e.nettype_resolve_funcs_,
      e.nettype_canonical_, e.anonymous_program_names_,
      e.unit_hier_head_names_});
}

void UnitScopeTables::Put(UnitScopeTables tables, Elaborator& e) {
  e.typedefs_ = std::move(tables.typedefs);
  e.cu_param_scope_ = std::move(tables.cu_param_scope);
  e.cu_scope_names_ = std::move(tables.cu_scope_names);
  e.class_names_ = std::move(tables.class_names);
  e.aggregate_typedef_names_ = std::move(tables.aggregate_typedef_names);
  e.parameterized_class_names_ = std::move(tables.parameterized_class_names);
  e.td_array_dims_ = std::move(tables.td_array_dims);
  e.nettype_names_ = std::move(tables.nettype_names);
  e.nettype_resolve_funcs_ = std::move(tables.nettype_resolve_funcs);
  e.nettype_canonical_ = std::move(tables.nettype_canonical);
  e.anonymous_program_names_ = std::move(tables.anonymous_program_names);
  e.unit_hier_head_names_ = std::move(tables.unit_hier_head_names);
}

void UnitScopeTables::RunPreElaborationValidations(Elaborator& e) {
  auto& units = e.units_;
  if (units.views.empty()) {
    e.RunPreElaborationValidations();
    return;
  }
  const std::shared_ptr<UnitScopeTables> kFresh = Take(e);
  e.RunPreElaborationValidations();
  const std::shared_ptr<UnitScopeTables> kMerged = Take(e);
  auto all_typedefs = e.all_typedefs_;
  auto all_cu_param_scope = e.all_cu_param_scope_;
  // Each unit's own tables, registered from its own view. What registering
  // reports was reported once already, over the merged view above. The unit's
  // subroutines are then checked against them, which the merged view's would
  // answer with every unit's names.
  for (size_t k = 0; k < units.views.size(); ++k) {
    Put(*kFresh, e);
    e.unit_ = units.views[k];
    e.diag_.PushSuppress();
    e.RegisterCuScopeItems();
    e.diag_.PopSuppress();
    units.tables[k] = Take(e);
    ReportUnresolvedInUnitSubroutines(
        e.unit_,
        UnitScopeNames{e.cu_scope_names_, e.cu_param_scope_, e.typedefs_,
                       e.class_names_},
        e.pkg_provided_names_, e.diag_);
  }
  Put(*kMerged, e);
  e.all_typedefs_ = std::move(all_typedefs);
  e.all_cu_param_scope_ = std::move(all_cu_param_scope);
  e.unit_ = units.merged;
}

namespace {

// The unit's own entries of `from`, the ones under a bare name, added to `to`
// under `scope`'s name; a package's or a class's entry, "p::t", is the same in
// every unit and stands in `to` already.
template <typename Value>
void AddUnitScoped(std::unordered_map<std::string_view, Value>& to,
                   const std::unordered_map<std::string_view, Value>& from,
                   std::string_view scope, Arena& arena) {
  for (const auto& [name, value] : from) {
    if (name.find("::") != std::string_view::npos) continue;
    to.emplace(*arena.Create<std::string>(std::string(scope) +
                                          "::" + std::string(name)),
               value);
  }
}

}  // namespace

void UnitScopeTables::PopulateUnitTypeFacts(Elaborator& e,
                                            RtlirDesign* design) {
  for (size_t k = 0; k < e.units_.tables.size(); ++k) {
    const UnitScopeTables& unit = *e.units_.tables[k];
    RtlirDesign own;
    TypeNameFacts facts{own.type_widths,  own.type_kinds,   own.type_signed,
                        own.type_layouts, own.type_targets, own.type_ranges,
                        own.type_enums};
    PopulateTypeWidths({unit.typedefs, unit.aggregate_typedef_names, e.arena_},
                       facts);
    const std::string kScope = "$unit#" + std::to_string(k);
    AddUnitScoped(design->type_widths, own.type_widths, kScope, e.arena_);
    AddUnitScoped(design->type_kinds, own.type_kinds, kScope, e.arena_);
    AddUnitScoped(design->type_signed, own.type_signed, kScope, e.arena_);
    AddUnitScoped(design->type_layouts, own.type_layouts, kScope, e.arena_);
    AddUnitScoped(design->type_targets, own.type_targets, kScope, e.arena_);
    AddUnitScoped(design->type_ranges, own.type_ranges, kScope, e.arena_);
    AddUnitScoped(design->type_enums, own.type_enums, kScope, e.arena_);
  }
}

UnitScopeTables::Switch::Switch(Elaborator& e, const ModuleDecl* decl) : e_(e) {
  auto& units = e.units_;
  auto it = units.owner.find(decl);
  if (it == units.owner.end() || it->second == units.current) return;
  saved_ = Take(e);
  saved_unit_ = e.unit_;
  saved_current_ = units.current;
  Put(*units.tables[it->second], e);
  e.unit_ = units.views[it->second];
  units.current = it->second;
}

UnitScopeTables::Switch::~Switch() {
  if (saved_ == nullptr) return;
  Put(std::move(*saved_), e_);
  e_.unit_ = saved_unit_;
  e_.units_.current = saved_current_;
}

}  // namespace delta
