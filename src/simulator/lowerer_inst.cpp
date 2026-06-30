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
         binding.direction == Direction::kInout ||
         binding.direction == Direction::kRef;
}

static Expr* MakeLocalPortId(std::string_view port_name, Arena& arena) {
  auto* name_str = arena.Create<std::string>(std::string(port_name));
  auto* local_id = arena.Create<Expr>();
  local_id->kind = ExprKind::kIdentifier;
  local_id->text = *name_str;
  return local_id;
}

static const RtlirPort* FindChildPort(const RtlirModuleInst& inst,
                                      std::string_view name) {
  for (const auto& p : inst.resolved->ports) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

// §25.3.2: an interface passed through a port shares its members with the
// connected interface instance. Alias each member of the child interface port
// (mem.a.member) onto the connected instance's member (sb_intf.member) so reads
// and writes through the port reach the shared storage. Returns true when the
// binding was an interface port (handled here, skipping the scalar path). Alias
// keys are interned in the arena because the SimContext maps key by string_view
// and these member names are not otherwise created.
bool Lowerer::TryAliasInterfacePort(const RtlirModuleInst& inst,
                                    const RtlirPortBinding& binding) {
  const RtlirPort* port = FindChildPort(inst, binding.port_name);
  if (!port || !port->is_interface_port || port->interface_type_name.empty()) {
    return false;
  }
  if (!binding.connection ||
      binding.connection->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto it = design_->all_modules.find(port->interface_type_name);
  if (it == design_->all_modules.end()) return false;
  const RtlirModule* ifc = it->second;

  std::string port_prefix = inst_prefix_ + std::string(inst.inst_name) + "." +
                            std::string(binding.port_name) + ".";
  std::string conn_prefix =
      inst_prefix_ + std::string(binding.connection->text) + ".";
  for (const auto& var : ifc->variables) {
    auto* alias =
        arena_.Create<std::string>(port_prefix + std::string(var.name));
    ctx_.AliasVariable(*alias, conn_prefix + std::string(var.name));
  }
  for (const auto& net : ifc->nets) {
    auto* alias =
        arena_.Create<std::string>(port_prefix + std::string(net.name));
    ctx_.AliasNet(*alias, conn_prefix + std::string(net.name));
  }
  return true;
}

void Lowerer::LowerPortBindings(const RtlirModuleInst& inst,
                                bool from_program) {
  // §23.3.2: the caller lowers bindings under the PARENT prefix; qualify the
  // port (local) side with the child segment ("u0.a") so the connection side
  // stays bare and resolves in the parent. Otherwise an implicit/wildcard
  // connection (.a == .a(a)) resolves to the child's own same-named port and
  // self-assigns instead of propagating.
  std::string inst_seg = std::string(inst.inst_name) + ".";
  for (const auto& binding : inst.port_bindings) {
    if (TryAliasInterfacePort(inst, binding)) continue;
    if (!IsConnectablePortBinding(binding)) continue;

    auto* local_id =
        MakeLocalPortId(inst_seg + std::string(binding.port_name), arena_);

    // §23.3.3 ref ports and §23.3.3.4 inout ports both share storage with the
    // connected parent signal, so alias the child port onto it rather than
    // lowering a one-way continuous assignment.
    if (binding.direction == Direction::kInout ||
        binding.direction == Direction::kRef) {
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

    // The output drives its connection; besides a bare net this may be a
    // part-select, element select, or concatenation produced by §23.3.3.5
    // instance-array distribution, all of which the continuous-assignment
    // lvalue writer now handles.
    ExprKind ck = binding.connection->kind;
    if (ck != ExprKind::kIdentifier && ck != ExprKind::kSelect &&
        ck != ExprKind::kConcatenation && ck != ExprKind::kAssignmentPattern &&
        ck != ExprKind::kStreamingConcat && ck != ExprKind::kMemberAccess) {
      continue;
    }
    RtlirContAssign ca;
    ca.lhs = binding.connection;
    ca.rhs = local_id;
    ca.width = binding.width;
    LowerContAssign(ca, from_program);
  }
}

}  // namespace delta
