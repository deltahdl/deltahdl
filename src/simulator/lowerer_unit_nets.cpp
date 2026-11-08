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
