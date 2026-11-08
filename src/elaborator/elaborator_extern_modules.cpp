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

static bool ExternPortTypesEquivalent(const DataType& a, const DataType& b) {
  return a.kind == b.kind && a.is_signed == b.is_signed &&
         a.type_name == b.type_name;
}

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

static ModuleDecl* FindExternDeclFor(const ModuleDecl* mod,
                                     const std::vector<ModuleDecl*>& decls) {
  for (auto* other : decls) {
    if (other->is_extern && other->name == mod->name) return other;
  }
  return nullptr;
}

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

static bool ValueParamTypesDiffer(const ModuleDecl* mod,
                                  const ModuleDecl* extern_decl, size_t i) {
  const DataType& mt = mod->param_types.at(i);
  const DataType& et = extern_decl->param_types.at(i);
  if (mt.kind == DataTypeKind::kImplicit || et.kind == DataTypeKind::kImplicit)
    return false;
  return !ExternPortTypesEquivalent(mt, et);
}

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
    if (!mp_is_type && ValueParamTypesDiffer(mod, extern_decl, i)) {
      diag.Error(mod->range.start,
                 std::format("{} '{}' parameter '{}' at position {} is "
                             "declared with a data type not equivalent to the "
                             "extern declaration's",
                             ElementWord(mod), mod->name, mp_name, i),
                 Subclause("23.5"));
      break;
    }
  }
}

static void ImportExternWildcardHeader(ModuleDecl* mod,
                                       const ModuleDecl* extern_decl) {
  if (mod->ports.empty()) mod->ports = extern_decl->ports;
  if (!mod->params.empty() || extern_decl->params.empty()) return;
  mod->params = extern_decl->params;
  mod->param_types = extern_decl->param_types;
  mod->param_port_locs = extern_decl->param_port_locs;
  mod->param_port_unpacked_dims = extern_decl->param_port_unpacked_dims;
  mod->localparam_port_names = extern_decl->localparam_port_names;
  mod->type_param_names = extern_decl->type_param_names;
  mod->has_param_port_list = extern_decl->has_param_port_list;
}

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
