// §23.5 (printed page 752): an extern module declaration gives a module's
// name, parameters and ports ahead of its definition, and the definition has
// to match it -- port count, port kinds and types, and parameters -- or take
// its header wholesale through `.*`. Syntax 24-1 and Syntax 25-1 give a
// program and an interface the same extern header. ResolveExternModules
// checks each module, interface and program that has such a declaration
// against it. Split out of elaborator_resolve.cpp, which resolves the rest of
// the compilation unit's cross-references.

#include <cstddef>
#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// Two port data types correspond for extern-declaration matching when they
// share a base kind, signedness, and (for named types) the same type name.
// Packed/unpacked dimension sizes are parameter-dependent expressions that are
// not yet evaluated here, so only the dimension-independent attributes that the
// parser records are compared.
static bool ExternPortTypesEquivalent(const DataType& a, const DataType& b) {
  return a.kind == b.kind && a.is_signed == b.is_signed &&
         a.type_name == b.type_name;
}

// The noun a diagnostic names the design element by: Syntax 24-1 and Syntax
// 25-1 give a program and an interface the extern header §23.5 describes for
// a module, so the definition being matched can be any of the three.
static std::string_view ElementWord(const ModuleDecl* mod) {
  switch (mod->decl_kind) {
    case ModuleDeclKind::kInterface:
      return "interface";
    case ModuleDeclKind::kProgram:
      return "program";
    default:
      return "module";
  }
}

// Returns the matching extern declaration for an actual design element among
// the declarations of its own kind, or nullptr.
static ModuleDecl* FindExternDeclFor(const ModuleDecl* mod,
                                     const std::vector<ModuleDecl*>& decls) {
  for (auto* other : decls) {
    if (other->is_extern && other->name == mod->name) return other;
  }
  return nullptr;
}

// §23.5: checks that each port of the actual module corresponds to the extern
// declaration in name, direction, and (when both sides state it) type. Reports
// the first mismatch found.
static void CheckExternPortMatch(const ModuleDecl* mod,
                                 const ModuleDecl* extern_decl,
                                 DiagEngine& diag) {
  for (size_t i = 0; i < mod->ports.size(); ++i) {
    const PortDecl& ep = extern_decl->ports[i];
    const PortDecl& mp = mod->ports[i];
    if (!mp.name.empty() && !ep.name.empty() && mp.name != ep.name) {
      diag.Error(mod->range.start,
                 std::format("{} '{}' port '{}' at position {} does not "
                             "match extern declaration port '{}'",
                             ElementWord(mod), mod->name, mp.name, i, ep.name),
                 Subclause("23.5"));
      break;
    }
    // §23.5 requires the extern declaration to match the actual module in the
    // equivalent types of corresponding ports. Direction and data type are
    // only compared when the extern header states them: a non-ANSI extern
    // port list supplies names and positions alone and leaves the type to the
    // actual definition, so an unspecified side is treated as a match.
    if (ep.direction != Direction::kNone && mp.direction != Direction::kNone &&
        ep.direction != mp.direction) {
      diag.Error(mp.loc,
                 std::format("{} '{}' port '{}' direction does not match "
                             "extern declaration",
                             ElementWord(mod), mod->name, mp.name),
                 Subclause("23.5"));
      break;
    }
    if (ep.data_type.kind != DataTypeKind::kImplicit &&
        mp.data_type.kind != DataTypeKind::kImplicit &&
        !ExternPortTypesEquivalent(ep.data_type, mp.data_type)) {
      diag.Error(mp.loc,
                 std::format("{} '{}' port '{}' type does not match "
                             "extern declaration",
                             ElementWord(mod), mod->name, mp.name),
                 Subclause("23.5"));
      break;
    }
  }
}

// §23.5: checks the parameter list of the actual module against the extern
// declaration by name, position, and parameter kind (type vs. value). Reports
// the first mismatch found.
static void CheckExternParamMatch(const ModuleDecl* mod,
                                  const ModuleDecl* extern_decl,
                                  DiagEngine& diag) {
  if (extern_decl->params.size() != mod->params.size()) {
    diag.Error(mod->range.start,
               std::format("{} '{}' parameter count ({}) does not match "
                           "extern declaration ({})",
                           ElementWord(mod), mod->name, mod->params.size(),
                           extern_decl->params.size()),
               Subclause("23.5"));
    return;
  }
  // The parameter lists must also correspond by name and position.
  for (size_t i = 0; i < mod->params.size(); ++i) {
    std::string_view mp_name = mod->params[i].first;
    std::string_view ep_name = extern_decl->params[i].first;
    if (!mp_name.empty() && !ep_name.empty() && mp_name != ep_name) {
      diag.Error(mod->range.start,
                 std::format("{} '{}' parameter '{}' at position {} "
                             "does not match extern declaration "
                             "parameter '{}'",
                             ElementWord(mod), mod->name, mp_name, i, ep_name),
                 Subclause("23.5"));
      break;
    }
    // §23.5 also calls for equivalent parameter types. A type parameter and
    // a value parameter at the same position are not equivalent, so the
    // two declarations must agree on whether each entry is a type
    // parameter.
    bool mp_is_type = mod->type_param_names.count(mp_name) != 0;
    bool ep_is_type = extern_decl->type_param_names.count(ep_name) != 0;
    if (mp_is_type != ep_is_type) {
      diag.Error(mod->range.start,
                 std::format("{} '{}' parameter '{}' at position {} "
                             "does not match the parameter kind of the "
                             "extern declaration",
                             ElementWord(mod), mod->name, mp_name, i),
                 Subclause("23.5"));
      break;
    }
  }
}

// §23.5: `.*` places the extern declaration's header on the module. When the
// extern is ANSI the body declares no ports, so the extern's (typed,
// directioned) ports are imported directly; when the extern is non-ANSI the
// body supplied the directions via non-ANSI port declarations, which already
// populated mod->ports, so those are kept rather than overwritten with the
// extern's name-only ports. §6.20.3: a type parameter's default type is carried
// in param_types (parallel to params), so it is imported alongside the names --
// otherwise a `.*` module whose ports are typed by an imported type parameter
// would leave that parameter with no default type.
static void ImportExternWildcardHeader(ModuleDecl* mod,
                                       const ModuleDecl* extern_decl) {
  if (mod->ports.empty()) mod->ports = extern_decl->ports;
  if (!mod->params.empty() || extern_decl->params.empty()) return;
  mod->params = extern_decl->params;
  mod->param_types = extern_decl->param_types;
  mod->type_param_names = extern_decl->type_param_names;
  mod->has_param_port_list = extern_decl->has_param_port_list;
}

// §23.5: matches one design element against the extern declaration of its
// name among `decls`, or takes that declaration's header through `.*`.
static void ResolveExternDecl(ModuleDecl* mod,
                              const std::vector<ModuleDecl*>& decls,
                              DiagEngine& diag) {
  if (mod->is_extern) return;

  ModuleDecl* extern_decl = FindExternDeclFor(mod, decls);
  if (!extern_decl) return;

  if (mod->has_wildcard_ports) {
    ImportExternWildcardHeader(mod, extern_decl);
    return;
  }

  if (extern_decl->ports.size() != mod->ports.size()) {
    diag.Error(mod->range.start,
               std::format("{} '{}' port count ({}) does not match "
                           "extern declaration ({})",
                           ElementWord(mod), mod->name, mod->ports.size(),
                           extern_decl->ports.size()),
               Subclause("23.5"));
    return;
  }
  CheckExternPortMatch(mod, extern_decl, diag);
  CheckExternParamMatch(mod, extern_decl, diag);
}

void Elaborator::ResolveExternModules() {
  for (const auto* decls :
       {&unit_->modules, &unit_->interfaces, &unit_->programs}) {
    for (auto* mod : *decls) ResolveExternDecl(mod, *decls, diag_);
  }
}

}  // namespace delta
