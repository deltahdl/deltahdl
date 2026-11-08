#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

struct RtlirBidirSwitch {
  GateKind kind = GateKind::kTran;
  Expr* terminal_a = nullptr;
  Expr* terminal_b = nullptr;
  Expr* control = nullptr;
  Expr* turn_on_delay = nullptr;
  Expr* turn_off_delay = nullptr;
};

struct RtlirUdpInst {
  const UdpDecl* decl = nullptr;
  const ModuleItem* source_item = nullptr;
  std::string_view name;
  std::optional<int64_t> array_index;
  SourceLoc loc;
  Expr* output = nullptr;
  std::vector<Expr*> inputs;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
};

}  // namespace delta
