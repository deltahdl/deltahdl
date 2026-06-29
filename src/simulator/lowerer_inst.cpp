#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

namespace delta {

static bool IsConnectablePortBinding(const RtlirPortBinding& binding) {
  if (!binding.connection) return false;
  if (binding.width == 0) return false;
  return binding.direction == Direction::kInput ||
         binding.direction == Direction::kOutput ||
         binding.direction == Direction::kInout;
}

static Expr* MakeLocalPortId(std::string_view port_name, Arena& arena) {
  auto* name_str = arena.Create<std::string>(std::string(port_name));
  auto* local_id = arena.Create<Expr>();
  local_id->kind = ExprKind::kIdentifier;
  local_id->text = *name_str;
  return local_id;
}

void Lowerer::LowerPortBindings(const RtlirModuleInst& inst,
                                bool from_program) {
  // §23.3.2: the caller lowers bindings under the PARENT prefix; qualify the
  // port (local) side with the child segment ("u0.a") so the connection side
  // stays bare and resolves in the parent. Otherwise an implicit/wildcard
  // connection (.a == .a(a)) resolves to the child's own same-named port and
  // self-assigns instead of propagating.
  const std::string inst_seg = std::string(inst.inst_name) + ".";
  for (const auto& binding : inst.port_bindings) {
    if (!IsConnectablePortBinding(binding)) continue;

    auto* local_id =
        MakeLocalPortId(inst_seg + std::string(binding.port_name), arena_);

    if (binding.direction == Direction::kInout) {
      if (binding.connection->kind != ExprKind::kIdentifier) continue;
      std::string local_qualified =
          inst_prefix_ + inst_seg + std::string(binding.port_name);
      std::string target = inst_prefix_ + std::string(binding.connection->text);
      ctx_.AliasVariable(local_qualified, target);
      continue;
    }

    if (binding.direction == Direction::kInput) {
      RtlirContAssign ca;
      ca.lhs = local_id;
      ca.rhs = binding.connection;
      ca.width = binding.width;
      LowerContAssign(ca, from_program);
      continue;
    }

    if (binding.connection->kind != ExprKind::kIdentifier) continue;
    RtlirContAssign ca;
    ca.lhs = binding.connection;
    ca.rhs = local_id;
    ca.width = binding.width;
    LowerContAssign(ca, from_program);
  }
}

}  // namespace delta
