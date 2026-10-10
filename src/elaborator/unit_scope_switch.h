#pragma once

#include <cstddef>
#include <memory>

#include "elaborator/elaborator.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct RtlirDesign;

// §3.12.1 (printed page 56) with §3.13: what the elaborator has registered of
// one compilation unit's scope -- its typedefs, parameters, classes, nettypes
// and other names -- which Elaborator::RegisterCuScopeItems fills before any
// design element is elaborated. In a compilation where each file is a unit of
// its own, every unit has its own, and a design element is elaborated with the
// tables of the unit that declared it in force.
struct UnitScopeTables {
  decltype(Elaborator::typedefs_) typedefs;
  decltype(Elaborator::cu_param_scope_) cu_param_scope;
  decltype(Elaborator::cu_scope_names_) cu_scope_names;
  decltype(Elaborator::class_names_) class_names;
  decltype(Elaborator::aggregate_typedef_names_) aggregate_typedef_names;
  decltype(Elaborator::parameterized_class_names_) parameterized_class_names;
  decltype(Elaborator::td_array_dims_) td_array_dims;
  decltype(Elaborator::nettype_names_) nettype_names;
  decltype(Elaborator::nettype_resolve_funcs_) nettype_resolve_funcs;
  decltype(Elaborator::nettype_canonical_) nettype_canonical;
  decltype(Elaborator::anonymous_program_names_) anonymous_program_names;
  decltype(Elaborator::unit_hier_head_names_) unit_hier_head_names;

  // The tables `e` holds now.
  static std::shared_ptr<UnitScopeTables> Take(const Elaborator& e);
  // Puts `tables` in force in `e`, moving them in.
  static void Put(UnitScopeTables tables, Elaborator& e);

  // Elaborator::RunPreElaborationValidations, over the merged view where `e`
  // elaborates several units, followed by each unit's own tables.
  static void RunPreElaborationValidations(Elaborator& e);

  // §6.18 with §3.12.1: what each unit's own typedefs say of their names --
  // widths, kinds, layouts and the rest of RtlirDesign's type tables -- under
  // the unit's scope name, "$unit#k::t", beside the bare names the merged
  // view's typedefs answer for, so the run asks the running code's unit's
  // first. Nothing where `e` elaborates one unit.
  static void PopulateUnitTypeFacts(Elaborator& e, RtlirDesign* design);

  // Runs `check` over each unit as parsed, which holds its own declarations
  // alone, where `e` elaborates several units, and over the one unit `e`
  // elaborates otherwise. For a check whose subject is one unit's
  // declarations judged against that unit alone.
  template <typename Check>
  static void ForEachUnit(Elaborator& e, Check check) {
    if (e.units_.units.empty()) {
      check();
      return;
    }
    CompilationUnit* saved = e.unit_;
    for (auto* unit : e.units_.units) {
      e.unit_ = unit;
      check();
    }
    e.unit_ = saved;
  }

  // Puts in force, while it lives, the scope of the unit that declared a design
  // element, where that is not the unit already in force.
  class Switch {
   public:
    Switch(Elaborator& e, const ModuleDecl* decl);
    ~Switch();
    Switch(const Switch&) = delete;
    Switch& operator=(const Switch&) = delete;

   private:
    Elaborator& e_;
    std::shared_ptr<UnitScopeTables> saved_;
    CompilationUnit* saved_unit_ = nullptr;
    size_t saved_current_ = 0;
  };
};

}  // namespace delta
