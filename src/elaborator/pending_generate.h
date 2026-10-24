#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/type_eval.h"

namespace delta {

struct Expr;
struct ModuleDecl;
struct ModuleItem;
struct RtlirModule;

// §27.5 selects a conditional generate's block by constant expressions
// evaluated during elaboration, and this elaborator evaluates that expression
// in Elaborator::ResolveDefparamsAndGenerates, after
// Elaborator::ElaborateModule has returned for every module. §26.3 makes an
// imported name locally visible only before that point in the current scope,
// so the condition has to fold against the scope of the module the generate
// was written in and not against the union of every module's imports.
// typedefs and cu_param_scope carry that scope:
// Elaborator::ElaborateBehavioralItem copies typedefs_ and cu_param_scope_
// into them as it queues the item, and Elaborator::ProcessPendingGenerate
// installs them again around the fold and the elaboration of the selected
// body, whose own declarations read typedefs_ as well.
//
// func_decls carries the same scope for §13.4.3, which has a constant
// function call evaluated during elaboration. Elaborator::ElaborateItems
// fills func_decls_ from the ModuleDecl it is elaborating and
// ItemElaborationStateSaver puts it back to what it held before that module,
// so the module's own functions are gone by the time
// Elaborator::ResolveDefparamsAndGenerates runs and only a copy taken at the
// queue site names them.
struct PendingGenerate {
  ModuleItem* item;
  RtlirModule* mod;
  TypedefMap typedefs;
  ScopeMap cu_param_scope;
  std::unordered_map<std::string_view, const ModuleItem*> func_decls;
  // §16.12: the module's property and sequence declarations, which an
  // assertion in the selected body instantiates by name; property_registry_
  // is per-module state as func_decls_ is, gone by the time the generate is
  // elaborated, so the copy taken at the queue site is what names them.
  PropertyRegistry property_registry;
  // §33.4.1.3, §33.4.1.5: the configuration's name for the instance holding
  // the generate and that instance's library, which a rule for an instance
  // inside the block is matched against and a search there starts from.
  std::string config_inst_path;
  std::string library;
  // §25.3 with §23.9: the module's interface instances by name, which an
  // interface port connection written in the selected body may name;
  // interface_inst_types_ is per-module state as func_decls_ is.
  std::unordered_map<std::string_view, std::string_view> interface_inst_types;
  // §25.3: the declarations of the module and of those enclosing it, through
  // whose instances an interface port connection written in the body may
  // reach an interface instance; module_decl_path_ is per-module state too.
  std::vector<const ModuleDecl*> module_decl_path;
  // §3.13 (e) with §6.18: the unpacked dimensions of the array typedefs the
  // module's scope holds, which a declaration in the selected body written
  // with one of their names takes; td_array_dims_ is per-module state as
  // typedefs_ is.
  std::unordered_map<std::string_view, std::vector<Expr*>> td_array_dims;
};

}  // namespace delta
