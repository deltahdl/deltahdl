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

// §23.2.2.1: diagnose redeclaration of a declared name against the ANSI and
// complete non-ANSI port name tables.
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

// §23.2.2.1: reconcile a declaration against an earlier partial
// (direction-only) port declaration — width mismatch is an error — and record
// the name, diagnosing any plain redeclaration. §3.13 (g) has the first net or
// variable of a port's name reintroduce it in the module name space, so a
// second one is a redeclaration there like any other. `kind_word` selects
// "net" or "variable" in the vector-range message.
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
    // §27.4: each generate-loop iteration is a distinct block instance, so the
    // name is tracked under its generate-prefixed (scoped) form; an unprefixed
    // top-level declaration scopes to its bare name, leaving that case
    // unchanged. Only a true same-scope clash collides.
    //
    // §6.5 closes with the rule that within a name space a name a net or
    // variable declared is not redeclared, and §23.9 states the general rule
    // that an identifier declares one item in a scope. A net or variable
    // reusing a net's or variable's name is the case §6.5 names and is filed
    // there, which is where sv-tests tags 6.5--variable_redeclare.sv; a clash
    // with a declaration of another kind keeps §23.9.
    diag.Error(item->loc, std::format("redeclaration of '{}'", item->name),
               Subclause(tables.redeclares_net_or_variable ? "6.5" : "23.9"));
  }
}

// §23.2.2.1: diagnose redeclaration of a declared name and width mismatches
// against an earlier partial (direction-only) port declaration. `kind_word`
// selects "net" or "variable" in the vector-range message.
void CheckDeclRedeclaration(const ModuleItem* item,
                            const DeclTypeRef& decl_type, DeclNameTables tables,
                            std::string_view kind_word, DiagEngine& diag) {
  CheckPortNameRedeclaration(item, tables, diag);
  CheckPartialPortOrNameRedeclaration(item, decl_type, tables, kind_word, diag);
}

// §3.13 (g) (printed page 58): a port's name may be reintroduced in the module
// name space only by a net or variable of that name, which
// CheckDeclRedeclaration reconciles with the port, so a declaration of any
// other kind taking it in the module itself is a redeclaration under §3.13's
// closing rule. A generate block is a scope of its own (§27.4), whose names do
// not reach the ports. Every other name enters §3.13 (e)'s one module name
// space under its generate-prefixed form, where a second declaration of it is
// the redeclaration §23.9 states.
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
