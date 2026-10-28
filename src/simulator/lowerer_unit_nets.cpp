// §3.12.1 (printed page 56 of IEEE 1800-2023) with §6.7 (printed 109): the
// nets the compilation-unit scope declares, each given the storage of a net of
// its declared net type and width ahead of every module, under the
// "$unit.name" key the unit's variables stand under, to which each module that
// does not declare the name is bound (AliasUnitDataItems).

#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/unit_scope_items.h"

namespace delta {

// The record of the net `item` declares, as Elaborator::ElaborateNetDecl
// builds a module's: the net type its keyword wrote, its width and
// signedness, and the declared type where a packed dimension addresses its
// bits over the range as written.
static RtlirNet UnitNetRecord(const ModuleItem& item, SimContext& ctx) {
  RtlirNet net;
  net.name = item.name;
  net.loc = item.loc;
  net.net_type = WrittenNetType(item.data_type);
  net.width = DeclaredTypeWidth(item.data_type, ctx);
  net.is_signed = item.data_type.is_signed;
  if (item.data_type.packed_dim_left != nullptr) net.dtype = &item.data_type;
  return net;
}

void CreateUnitNets(const RtlirDesign* design, SimContext& ctx, Arena& arena) {
  ForEachUnitScope(design, arena,
                   [&](const CompilationUnit& unit, std::string_view scope) {
                     for (const ModuleItem* item : unit.cu_items) {
                       if (item->kind != ModuleItemKind::kNetDecl) continue;
                       std::string_view key = *arena.Create<std::string>(
                           std::string(scope) + "." + std::string(item->name));
                       CreateDeclaredNet(key, UnitNetRecord(*item, ctx),
                                         design->cu_timescale, ctx, arena);
                     }
                   });
}

}  // namespace delta
