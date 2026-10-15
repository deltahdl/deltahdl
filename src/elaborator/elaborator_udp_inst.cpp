// §29.8 with §33.6: resolving the user-defined primitive an instance names
// through the library search and configuration rules, and elaborating its
// instances. Moved out of elaborator_items_udp.cpp, which reached the size
// the assert-no-oversized-source-files job fails at.

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/const_eval.h"
#include "elaborator/disable_iff_resolution.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/interface_property_instance.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

// §33.6.1: the libraries are searched in the order they were declared, and a
// name reaches the cell held by the first library searched that holds one. A
// primitive is such a cell, so the primitive a name reaches is the one in the
// earliest searched library holding a primitive of that name -- and it is
// reached at all only when no design element of another kind sits in a library
// searched before it. A name whose primitive is out-ranked that way is naming
// the other element, not a primitive instance, so this answers nullptr for it.
//
// Where no search order is in force every library sits at the same position, so
// the first primitive of the name answers and it outranks nothing, which is
// what a compilation given no library map sees.
//
// §33.6.2: a configuration may select the libraries to search instead, and a
// library its list leaves out is not searched at all. A primitive is a cell a
// library holds, so a primitive held only by a library left out of the list is
// skipped here rather than ranked behind the listed ones -- the name reaches no
// primitive, exactly as it reaches no module under the same list.
//
// §33.6.3: a cell selection clause paired with a use expansion instead binds
// every cell of the selected name outright to the one library.cell the clause
// names, so where such a clause applies there is no search to rank libraries in
// and no list to exclude one. The name reaches the primitive the clause names
// even when the selected library list leaves that library out, and reaches no
// primitive at all when the clause names a cell of some other kind -- or names
// nothing that exists -- since a clause that has bound the name has settled it.
//
// §33.6.4: an instance selection clause naming a library list puts that list in
// force over the instance it names, and the list is inherited by every
// descendant of that instance. A primitive instantiated anywhere in that
// subhierarchy is therefore searched for in the inherited list rather than in
// the one the configuration's default clause named -- reaching a primitive the
// default clause's list would have excluded, and reaching none where the
// inherited list holds none, whatever the default clause's list holds.
namespace {

// The primitive named `name` whose library stands earliest in `order`, or
// nullptr where the list excludes every one of them. `nearest_pos` takes the
// position of the one answered, which is what a cell of another kind is ranked
// against afterwards.
UdpDecl* NearestUdpInSearchOrder(const CompilationUnit* unit,
                                 std::string_view name,
                                 const std::vector<std::string>& order,
                                 bool strict, size_t* nearest_pos) {
  UdpDecl* nearest = nullptr;
  for (auto* u : unit->udps) {
    if (u->name != name) continue;
    if (LibraryExcludedBySelectedList(u->library, order, strict)) continue;
    size_t pos = LibrarySearchPosition(u->library, order);
    // A definition answers before an extern prototype of it in one library.
    const bool kDefinesPrototype = nearest != nullptr && pos == *nearest_pos &&
                                   nearest->is_extern && !u->is_extern;
    if (nearest == nullptr || pos < *nearest_pos || kDefinesPrototype) {
      nearest = u;
      *nearest_pos = pos;
    }
  }
  return nearest;
}

}  // namespace

// §33.4.1.4/§33.4.1.6: the primitive a cell clause's use expansion binds every
// cell of `name` to. Nullopt where no clause selects the name, so the search
// below runs; a present value (possibly nullptr) is the binding, where nullptr
// means the named target does not exist.
std::optional<UdpDecl*> Elaborator::ResolveUdpUseOverride(
    std::string_view name) const {
  auto clause = cell_clause_use_overrides_.find(std::string(name));
  if (clause == cell_clause_use_overrides_.end()) return std::nullopt;
  if (!CellUseOverrideApplies(clause->second.src_lib, name, unit_)) {
    return std::nullopt;
  }
  // An omitted target library is inherited from the parent cell (§33.4.1.6).
  const auto& ov = clause->second;
  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  return FindUdpInLibrary(target_lib, ov.use_cell, unit_);
}

UdpDecl* Elaborator::FindUdpByName(std::string_view name) const {
  if (auto bound = ResolveUdpUseOverride(name); bound.has_value()) {
    return *bound;
  }

  // The list the instance selection clause covering this instance passes down,
  // where there is one, in place of the one the default clause put in force. A
  // clause names its list outright, so the list it hands down is a list in
  // force wherever it reaches.
  const std::vector<std::string>* inherited =
      InstanceLiblistForPath(config_inst_path_, instance_liblist_overrides_);
  const std::vector<std::string>& order =
      inherited == nullptr ? library_order_ : *inherited;
  bool strict = inherited != nullptr || library_order_strict_;

  size_t nearest_pos = 0;
  UdpDecl* nearest =
      NearestUdpInSearchOrder(unit_, name, order, strict, &nearest_pos);
  if (nearest == nullptr) return nullptr;

  const ModuleDecl* other_kind = FindModule(name);
  if (other_kind == nullptr) return nearest;
  size_t other_pos = LibrarySearchPosition(other_kind->library, order);
  if (other_pos < nearest_pos) return nullptr;
  return nearest;
}

// §29.8 gives a UDP instance a gate's delay2, at most two delays and those
// written in order. Read before the primitive's declaration, `#( ... )` is the
// parameter override of what the parser took for a module, so its ordered
// values are the instance's rise and fall delays, a third is more than a UDP
// takes, and a named assignment is no delay at all.
static void TakeForwardUdpDelays(ModuleItem* item, DiagEngine& diag) {
  const auto& params = item->inst_params;
  if (params.empty()) return;
  bool named = std::any_of(params.begin(), params.end(),
                           [](const auto& p) { return !p.first.empty(); });
  if (named) {
    diag.Error(item->loc,
               "a UDP instance takes its delays in order, not a named "
               "assignment",
               Subclause("29.8"));
  } else if (params.size() > 2) {
    diag.Error(item->loc, "UDP instantiation shall have at most two delays",
               Subclause("29.8"));
  }
  if (!named) {
    item->gate_delay = params[0].second;
    if (params.size() > 1) item->gate_delay_fall = params[1].second;
  }
  item->inst_params.clear();
}

// §29.8 connects a UDP instance's terminals in the order its definition gives,
// and Syntax 29-2 writes them as terminals alone, so neither a named
// connection nor `.*`, which a module instance may write, is among them.
static void ReportNamedUdpConnections(const ModuleItem* item,
                                      DiagEngine& diag) {
  bool named = item->inst_wildcard ||
               std::any_of(item->inst_ports.begin(), item->inst_ports.end(),
                           [](const auto& p) { return !p.first.empty(); });
  if (!named) return;
  diag.Error(item->loc,
             "a UDP instance connects its terminals in order, not by name",
             Subclause("29.8"));
}

void Elaborator::ReclassifyForwardUdpInstances(const ModuleDecl* decl) {
  for (auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;

    // §33.6.4: a library list a configuration named for one instance governs
    // that instance, and this walk runs while the cell holding the
    // instantiation is being elaborated -- one level above the path such a
    // clause would carry. The search is therefore made under the
    // instantiation's own path, and the path is put back afterwards, so a
    // clause naming this very instance is the one the primitive is looked for
    // under. An instantiation with no instance name adds no level to reach.
    std::string saved_inst_path = config_inst_path_;
    if (!item->inst_name.empty()) {
      config_inst_path_ =
          HierInstancePath(config_inst_path_, gen_block_path_, item->inst_name);
    }
    UdpDecl* udp = FindUdpByName(item->inst_module);
    config_inst_path_ = std::move(saved_inst_path);
    if (udp == nullptr) continue;

    ReportNamedUdpConnections(item, diag_);
    TakeForwardUdpDelays(item, diag_);
    item->kind = ModuleItemKind::kUdpInst;
    item->gate_inst_name = item->inst_name;
    item->inst_name = {};
    item->gate_terminals.clear();
    item->gate_terminals.reserve(item->inst_ports.size());
    for (const auto& [pname, pexpr] : item->inst_ports) {
      item->gate_terminals.push_back(pexpr);
    }
    item->inst_ports.clear();
    item->inst_ports_implicit.clear();
  }
}

// §29.8: the terminals connect in the order the UDP definition gives, and A.5.4
// writes that connection as `( output_terminal , input_terminal { ,
// input_terminal } )` -- one terminal for the output port §29.3.1 makes the
// first of the port list, and one for each input port the same list names. The
// count is therefore the header's and not the instantiation's to choose: an
// instantiation carrying some other number of terminals leaves an input port
// with nothing driving it or names a terminal no port receives.
//
// Nothing downstream says so. Elaborator::ElaborateOneUdpInst below splits the
// list at index 1 whatever its length, and UdpRowMatchesLevels
// (src/simulator/udp_eval.cpp) compares that length against each row's field
// count and answers no match when they differ, so every row of the table is
// passed over and the instance drives §29.3.4's default of x for the whole run.
//
// Says nothing where the primitive declared no inputs.
// Parser::ValidateUdpHeader (src/parser/parser_udp.cpp) has already reported
// that header, and the count this would name is the one already being reported.
static void CheckUdpInstTerminalCount(const ModuleItem* item,
                                      const UdpDecl* decl, DiagEngine& diag) {
  if (decl->input_names.empty()) return;
  size_t declared = decl->input_names.size() + 1;
  if (item->gate_terminals.size() == declared) return;
  diag.Error(
      item->loc,
      std::format("primitive '{}' takes {} terminal(s) but this instance "
                  "connects {}",
                  decl->name, declared, item->gate_terminals.size()),
      Subclause("29.8"));
}

// §29.8: records on `mod` every instance of a user-defined primitive that one
// instantiation writes, so that the primitive drives the nets its output
// terminals name. A UDP is instantiated inside a module the way a gate is
// (§28.3), and a gate instance reaches simulation as the RtlirContAssign
// ElaborateGateInst (src/elaborator/elaborator_gates.cpp) appends; a primitive
// instance reaches it as the RtlirUdpInst Elaborator::ElaborateOneUdpInst
// appends. Append nothing and no instance's output terminal has a driver.
void Elaborator::ElaborateUdpInst(ModuleItem* item, RtlirModule* mod) {
  // §29.8 reads the terminal count off the primitive's own port list, so it is
  // answered once for the instantiation rather than once per element of an
  // array: every element of an expanded array carries the terminal list written
  // here, and one list written wrong is one mistake.
  if (const UdpDecl* decl = FindUdpByName(item->inst_module); decl != nullptr) {
    CheckUdpInstTerminalCount(item, decl, diag_);
  }

  // §29.8: an array of UDP instances may carry an optional range, and the
  // terminal connection rules of §28.3.6 still apply, so such a range is
  // expanded here into one instance per array element the way ElaborateGateInst
  // (src/elaborator/elaborator_gates.cpp) expands the range on an array of
  // gates. ExpandInstanceArray (src/elaborator/elaborator_helpers.h) is that
  // one expansion, and it answers false where the range declares one instance
  // or names a bound it cannot fold, leaving the range to record the one
  // instance it describes.
  if (ExpandInstanceArray(item, mod, arena_, BuildParamScope(mod),
                          [this, mod](ModuleItem* element) {
                            ElaborateOneUdpInst(element, mod);
                          }))
    return;

  ElaborateOneUdpInst(item, mod);
}

// §29.8: appends the one RtlirUdpInst that the terminal list currently held on
// `item` describes -- a single instance, or one element of an expanded instance
// array.
//
// Resolve the declaration here rather than record the name for a later pass.
// Elaborator::FindUdpByName answers the library search order §33.6 defines
// under the configuration in force at this point of the walk, and that
// configuration is not readable from the RtlirModule afterwards. Where it
// answers nullptr the name reaches no primitive, so nothing is appended and
// nothing is reported: the unresolved name is already reported elsewhere, and a
// second report would name the same source position twice.
//
// §29.8's `udp_instance` production puts the output terminal first --
// `[ name_of_instance ] ( output_terminal , input_terminal { , input_terminal }
// )` -- so ModuleItem::gate_terminals splits at index 1. ModuleItem::gate_kind
// is not consulted, because Parser::ParseOneUdpInstance
// (src/parser/parser_udp.cpp:6) never writes it for a primitive instance.
//
// §29.8 admits two delays and no more, since a UDP does not support z.
// ModuleItem::gate_delay and ModuleItem::gate_delay_fall are therefore carried
// and ModuleItem::gate_delay_decay is not.
//
// RtlirUdpInst::gen_block_consts and RtlirUdpInst::gen_block_prefixes are left
// at their defaults, which is what the gate path leaves on the RtlirContAssign
// it appends. Elaborator::ElaborateGenerateBlockItem
// (src/elaborator/elaborator_generate.cpp:122) stamps §27.4's loop-index values
// onto RtlirModule::processes and RtlirModule::assigns after the item is
// elaborated, and it does not stamp RtlirModule::udp_insts.
void Elaborator::ElaborateOneUdpInst(const ModuleItem* item, RtlirModule* mod) {
  const UdpDecl* decl = FindUdpByName(item->inst_module);
  if (decl == nullptr) return;
  if (item->gate_terminals.empty()) return;

  RtlirUdpInst inst;
  inst.decl = decl;
  inst.name = item->gate_inst_name;
  inst.loc = item->loc;
  inst.output = item->gate_terminals.front();
  inst.inputs.assign(item->gate_terminals.begin() + 1,
                     item->gate_terminals.end());
  inst.delay = item->gate_delay;
  inst.delay_fall = item->gate_delay_fall;
  inst.drive_strength0 = item->drive_strength0;
  inst.drive_strength1 = item->drive_strength1;
  mod->udp_insts.push_back(inst);
}

}  // namespace delta
