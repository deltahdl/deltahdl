#include <cstdint>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
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
// (direction-only) port declaration — width mismatch is an error — or, when
// there is no partial port, record the name and diagnose any plain
// redeclaration. `kind_word` selects "net" or "variable" in the vector-range
// message.
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
  } else if (!tables.declared_names.insert(tables.scoped_name).second) {
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

bool Elaborator::ReconcilePartialPortSignedness(std::string_view name,
                                                bool decl_signed,
                                                RtlirModule* mod) {
  // §23.2.2.1: the signed attribute may sit on the port direction declaration,
  // on the corresponding net/variable declaration, or on both; if either is
  // signed, the other is considered signed too.
  bool effective = decl_signed || non_ansi_signed_ports_.count(name) != 0;
  if (effective) {
    non_ansi_signed_ports_.insert(name);
    for (auto& p : mod->ports) {
      if (p.name == name) p.is_signed = true;
    }
  }
  return effective;
}

// §23.2.2.1: a net or variable declaration naming a port whose port declaration
// held no net or variable type declares that port's own object, so the port is
// of the declaration's kind -- a net of the net type it was declared with, or
// a variable where that net type is NetType::kNone. So `output f; logic f;`
// makes f a variable port, and `input a; wand a;` makes a a wand net port.
void GivePartialPortItsKind(std::string_view name, NetType net_type,
                            RtlirModule* mod) {
  for (auto& p : mod->ports) {
    if (p.name != name) continue;
    p.is_var = net_type == NetType::kNone;
    p.net_type = net_type;
  }
}

}  // namespace delta
