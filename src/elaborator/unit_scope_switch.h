#pragma once

#include <cstddef>
#include <memory>

#include "elaborator/elaborator.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct RtlirDesign;

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

  static std::shared_ptr<UnitScopeTables> Take(const Elaborator& e);
  static void Put(UnitScopeTables tables, Elaborator& e);

  static void RunPreElaborationValidations(Elaborator& e);

  static void PopulateUnitTypeFacts(Elaborator& e, RtlirDesign* design);

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
