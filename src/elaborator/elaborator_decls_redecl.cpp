#include <cstdint>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_module.h"

namespace delta {

static void CheckPortNameRedeclaration(const ModuleItem* item,
                                       const DeclNameTables& tables,
                                       DiagEngine& diag) {
  if (tables.ansi_port_names.count(item->name)) {
    diag.Error(item->loc,
               std::format("redeclaration of ANSI port '{}'", item->name),
               Subclause("23.2.2.1"));
  }
  if (tables.non_ansi_complete_ports.count(item->name)) {
    diag.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name),
        Subclause("23.2.2.1"));
  }
}

static void CheckPartialPortOrNameRedeclaration(const ModuleItem* item,
                                                const DeclTypeRef& decl_type,
                                                DeclNameTables tables,
                                                std::string_view kind_word,
                                                DiagEngine& diag) {
  auto it = tables.non_ansi_partial_ports.find(item->name);
  if (it != tables.non_ansi_partial_ports.end()) {
    uint32_t decl_width = EvalTypeWidth(decl_type.dtype, decl_type.typedefs);
    if (decl_width != it->second) {
      diag.Error(item->loc,
                 std::format("vector range of {} '{}' does not match its port "
                             "declaration",
                             kind_word, item->name),
                 Subclause("23.2.2.1"));
    }
  }
  if (!tables.declared_names.insert(tables.scoped_name).second) {
    diag.Error(item->loc, std::format("redeclaration of '{}'", item->name),
               Subclause(tables.redeclares_net_or_variable ? "6.5" : "23.9"));
  }
}

void CheckDeclRedeclaration(const ModuleItem* item,
                            const DeclTypeRef& decl_type, DeclNameTables tables,
                            std::string_view kind_word, DiagEngine& diag) {
  CheckPortNameRedeclaration(item, tables, diag);
  CheckPartialPortOrNameRedeclaration(item, decl_type, tables, kind_word, diag);
}

void Elaborator::DeclareInModuleNameSpace(std::string_view name,
                                          SourceLoc loc) {
  if (name.empty()) return;
  if (gen_prefix_.empty() && (ansi_port_names_.contains(name) ||
                              non_ansi_complete_ports_.contains(name) ||
                              non_ansi_partial_ports_.contains(name))) {
    diag_.Error(loc, std::format("redeclaration of port '{}'", name),
                Subclause("3.13"));
    return;
  }
  if (!declared_names_.insert(ScopedName(name)).second) {
    diag_.Error(loc, std::format("redeclaration of '{}'", name),
                Subclause("23.9"));
  }
}

bool Elaborator::ReconcilePartialPort(std::string_view name, bool decl_signed,
                                      NetType net_type, RtlirModule* mod) {
  if (non_ansi_partial_ports_.count(name) == 0) return decl_signed;
  bool effective = decl_signed || non_ansi_signed_ports_.count(name) != 0;
  if (effective) non_ansi_signed_ports_.insert(name);
  for (auto& p : mod->ports) {
    if (p.name != name) continue;
    if (effective) p.is_signed = true;
    p.is_var = net_type == NetType::kNone;
    p.net_type = net_type;
  }
  return effective;
}

}  // namespace delta
