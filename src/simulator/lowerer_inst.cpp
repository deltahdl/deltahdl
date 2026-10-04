#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"
#include "simulator/checker_actuals.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

// §23.2.2.1 (printed page 732), Example 3: a port written `a[7:4]` names no
// storage of its own but a select of the module's `a`, "First port is upper 4
// bits of 'a'", whose declaration `input [7:0] a` gives its direction and
// width. That vector is what is created for it, once however many ports select
// from it; a port with a name is created under the name. Nothing for a port
// that is neither.
void CreatePortStorage(const std::string& prefix, const RtlirPort& port,
                       SimContext& ctx, Arena& arena) {
  if (!port.name.empty()) {
    CreatePortVariable(
        *arena.Create<std::string>(prefix + std::string(port.name)), port, ctx,
        arena);
    return;
  }
  const Expr* root = port.port_expr;
  while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
  if (root == nullptr || root->kind != ExprKind::kIdentifier ||
      port.selected_width == 0) {
    return;
  }
  RtlirPort vector = port;
  vector.width = port.selected_width;
  CreatePortVariable(
      *arena.Create<std::string>(prefix + std::string(root->text)), vector, ctx,
      arena);
}

// An output port connection the continuous-assignment lvalue writer can drive:
// a bare net, or a part-select / element select / concatenation / member /
// streaming concatenation produced by §23.3.3.5 instance-array distribution.
static bool IsDrivableOutputConnection(ExprKind k) {
  return k == ExprKind::kIdentifier || k == ExprKind::kSelect ||
         k == ExprKind::kConcatenation || k == ExprKind::kAssignmentPattern ||
         k == ExprKind::kStreamingConcat || k == ExprKind::kMemberAccess;
}

// The data type of the port `binding` connects, kImplicit where the
// instance names no such port.
static DataTypeKind BoundPortType(const RtlirModuleInst& inst,
                                  const RtlirPortBinding& binding) {
  DataTypeKind type = DataTypeKind::kImplicit;
  for (const RtlirPort& port : inst.resolved->ports) {
    if (port.name == binding.port_name) type = port.type_kind;
  }
  return type;
}

// §6.16 and §6.17: a string and an event have no width, and a port of either
// type is connected all the same.
static bool IsConnectablePortBinding(const RtlirModuleInst& inst,
                                     const RtlirPortBinding& binding) {
  if (!binding.connection) return false;
  DataTypeKind type = BoundPortType(inst, binding);
  bool has_value = binding.width != 0 || type == DataTypeKind::kString ||
                   type == DataTypeKind::kEvent;
  return has_value && (binding.direction == Direction::kInput ||
                       binding.direction == Direction::kOutput ||
                       binding.direction == Direction::kInout ||
                       binding.direction == Direction::kRef);
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

// §23.2.2.2 (printed page 734): an explicitly named port specifies "elements
// ... declared in a module" on the port list, so the port stands for its
// expression, and its connection is joined to that expression inside the
// instance. The copy names each object the expression reads under the
// instance's segment, "u0.r" for r, as MakeLocalPortId names a port's own
// storage, so that it resolves from the parent's scope where the binding is
// lowered. A literal inside it is shared rather than copied.
static Expr* QualifiedPortExpr(const Expr* e, const std::string& inst_seg,
                               Arena& arena) {
  if (e == nullptr) return nullptr;
  auto* copy = arena.Create<Expr>(*e);
  if (e->kind == ExprKind::kIdentifier) {
    copy->text = *arena.Create<std::string>(inst_seg + std::string(e->text));
    return copy;
  }
  // A member access names its member, which is no object of the module.
  copy->lhs = QualifiedPortExpr(e->lhs, inst_seg, arena);
  if (e->kind != ExprKind::kMemberAccess) {
    copy->rhs = QualifiedPortExpr(e->rhs, inst_seg, arena);
  }
  copy->condition = QualifiedPortExpr(e->condition, inst_seg, arena);
  copy->true_expr = QualifiedPortExpr(e->true_expr, inst_seg, arena);
  copy->false_expr = QualifiedPortExpr(e->false_expr, inst_seg, arena);
  copy->base = QualifiedPortExpr(e->base, inst_seg, arena);
  copy->index = QualifiedPortExpr(e->index, inst_seg, arena);
  copy->index_end = QualifiedPortExpr(e->index_end, inst_seg, arena);
  copy->repeat_count = QualifiedPortExpr(e->repeat_count, inst_seg, arena);
  for (auto*& element : copy->elements) {
    element = QualifiedPortExpr(element, inst_seg, arena);
  }
  return copy;
}

// The name of the storage an inout or a ref port's connection is aliased to:
// the module's own object where the port is written `ref .Y(x)`, the port's
// name for every other port, and for one whose expression names no single
// object of the module.
static std::string_view PortStorageName(const RtlirPortBinding& binding) {
  if (binding.port_expr != nullptr &&
      binding.port_expr->kind == ExprKind::kIdentifier) {
    return binding.port_expr->text;
  }
  return binding.port_name;
}

// §25.5 (printed page 787): "the modport name is hierarchical from the
// interface instance" in a connection, `P pi(s.tb)`, which restricts the port
// to the modport's list without naming another instance, so the port shares
// the members of `s`. Returns the identifier naming the connected interface
// instance, or null where the connection names none.
static const Expr* ConnectedInterfaceInstance(const Expr* conn,
                                              std::string_view type_name,
                                              const CompilationUnit* cu) {
  if (conn == nullptr) return nullptr;
  if (conn->kind == ExprKind::kIdentifier) return conn;
  if (conn->kind != ExprKind::kMemberAccess || conn->lhs == nullptr ||
      conn->lhs->kind != ExprKind::kIdentifier || conn->rhs == nullptr ||
      conn->rhs->kind != ExprKind::kIdentifier || cu == nullptr) {
    return nullptr;
  }
  for (const ModuleDecl* ifc : cu->interfaces) {
    if (ifc->name != type_name) continue;
    for (const ModportDecl* mp : ifc->modports) {
      if (mp->name == conn->rhs->text) return conn->lhs;
    }
  }
  return nullptr;
}

// §25.3.2: the interface port keyed `port_key` denotes the instance keyed
// `instance_key`, which is recorded for the port's name to stand for that
// instance as the head of a call through it (§25.7). §25.9: where a value is
// wanted, `v = b` or `v == b`, the port's name is that instance, so the
// storage CreatePortStorage gave the port holds the instance's handle.
static void BindPortToInstance(const std::string& port_key,
                               const std::string& instance_key, SimContext& ctx,
                               Arena& arena) {
  ctx.RegisterInterfacePortInstance(port_key, instance_key);
  if (Variable* own = ctx.FindVariable(port_key)) {
    own->value =
        MakeLogic4VecVal(arena, 64, ctx.VirtualInterfaceHandle(instance_key));
  }
}

// §25.3.2: the key of the interface instance a connection's head `name`
// denotes from the instance being lowered: the instance of that name, or,
// where `name` is an interface port of that instance, passed down a level,
// the instance connected to the port in turn.
std::string Lowerer::ConnectedInstanceKey(std::string_view name) const {
  std::string key = inst_prefix_ + std::string(name);
  std::string_view through_port = ctx_.FindInterfacePortInstance(key);
  return through_port.empty() ? key : std::string(through_port);
}

// The identifier at the head of an interface port's connection: the instance
// itself, `sb`, or the instance a modport connection names, `sb` of `sb.mp`;
// null for a connection of any other shape.
static const Expr* ConnectedInstanceHead(const Expr* conn) {
  if (conn == nullptr) return nullptr;
  if (conn->kind == ExprKind::kIdentifier) return conn;
  if (conn->kind == ExprKind::kMemberAccess && conn->lhs != nullptr &&
      conn->lhs->kind == ExprKind::kIdentifier) {
    return conn->lhs;
  }
  return nullptr;
}

// §25.3.3: the interface a port connects to and, in `instance`, the
// identifier naming the connected instance. An interface-typed port's own
// interface, and for a generic port, `interface a` or `interface.mp b`, which
// names none, the interface the connected instance is an instance of, which
// RegisterChildInstanceKeys has recorded by the time any port is bound. Null
// where the connection names no instance of a known interface.
const RtlirModule* Lowerer::ConnectedInterface(const RtlirPort& port,
                                               const Expr* conn,
                                               const Expr*& instance) const {
  std::string_view type_name = port.interface_type_name;
  if (type_name.empty()) {
    instance = ConnectedInstanceHead(conn);
    if (instance == nullptr) return nullptr;
    type_name = ctx_.FindInstanceType(ConnectedInstanceKey(instance->text));
  } else {
    instance =
        ConnectedInterfaceInstance(conn, type_name, design_->compilation_unit);
    if (instance == nullptr) return nullptr;
  }
  auto it = design_->all_modules.find(type_name);
  return it != design_->all_modules.end() ? it->second : nullptr;
}

// Registers `def` under `key`, interned by the caller, to run in the
// instance `inst_prefix` whatever instance the call names it through.
static void RegisterRunningIn(std::string_view key, ModuleItem* def,
                              const std::string& inst_prefix, SimContext& ctx) {
  ctx.RegisterFunction(key, def);
  GenBlockSubroutineScope scope;
  scope.inst_prefix = inst_prefix;
  ctx.RegisterGenBlockSubroutineScope(key, std::move(scope));
}

// §25.3.2 with §25.10: the interface's variables and its parameters, the
// `True` of `localparam True = 1;` among them, are members reached through
// the port's name, `b.True`, so each answers under the port's prefix for the
// connected instance's own.
static void AliasVariableMembers(const RtlirModule* ifc,
                                 const std::string& port_prefix,
                                 const std::string& conn_prefix,
                                 SimContext& ctx, Arena& arena) {
  auto alias = [&](std::string_view name) {
    auto* key = arena.Create<std::string>(port_prefix + std::string(name));
    ctx.AliasVariable(*key, conn_prefix + std::string(name));
  };
  for (const auto& var : ifc->variables) alias(var.name);
  for (const auto& param : ifc->params) alias(param.name);
}

// §25.5: the modport of `ifc` a port selects: the one its connection names,
// `i1.A`, or else the one its declaration names, `I.A i`; null where neither
// names one `ifc` declares.
static const ModportDecl* SelectedModport(const RtlirPort& port,
                                          const Expr* conn,
                                          const RtlirModule* ifc,
                                          const CompilationUnit* cu) {
  std::string_view name;
  if (conn != nullptr && conn->kind == ExprKind::kMemberAccess &&
      conn->rhs != nullptr && conn->rhs->kind == ExprKind::kIdentifier) {
    name = conn->rhs->text;
  } else if (port.dtype != nullptr) {
    name = port.dtype->modport_name;
  }
  if (name.empty() || cu == nullptr) return nullptr;
  for (const ModuleDecl* decl : cu->interfaces) {
    if (decl->name != ifc->name) continue;
    for (const ModportDecl* mp : decl->modports) {
      if (mp->name == name) return mp;
    }
  }
  return nullptr;
}

// §25.5.4: each modport expression port of the modport the port `port`
// selects, `.P(r[3:0])`, is recorded under the port's path to it,
// "u1.i.P", with the expression and the instance it is read and written in.
void Lowerer::RegisterModportExpressions(const RtlirPort& port,
                                         const Expr* conn,
                                         const RtlirModule* ifc,
                                         const std::string& port_key,
                                         const std::string& instance_key) {
  const ModportDecl* modport =
      SelectedModport(port, conn, ifc, design_->compilation_unit);
  if (modport == nullptr) return;
  for (const ModportPort& mp_port : modport->ports) {
    if (!mp_port.is_named_port || mp_port.expr == nullptr) continue;
    ctx_.RegisterModportExpression(
        port_key + "." + std::string(mp_port.name),
        ModportExpressionPort{mp_port.expr, instance_key + "."});
  }
}

// §25.7.4: whether the interface `ifc` declares the task `name` extern
// forkjoin, which more than one connected module may define.
static bool DeclaresForkjoin(const RtlirModule* ifc, std::string_view name) {
  for (const ModuleItem* proto : ifc->function_decls) {
    if (proto->name == name && proto->is_extern && proto->is_forkjoin)
      return true;
  }
  return false;
}

// §25.7.3: a module defines a task or function of the interface connected
// to its port `port_name`, `task a.Read(...)`, and exports it through the
// port's modport; the body runs in the defining instance and reads its
// declarations. Each such body is registered under the defining instance's
// path to it, "mem.a.Read", which a call reaches that instance's alone by
// (§25.7.4), and under the connected instance's key, "sb_intf.Read", which a
// call through the instance or a port bound to it resolves by. §25.7.4: a
// task the interface declares extern forkjoin may be defined by several
// connected modules, so each definition is added to the task's own instead,
// and a call runs them all.
void Lowerer::RegisterExportedSubroutines(const RtlirModuleInst& inst,
                                          std::string_view port_name,
                                          const RtlirModule* ifc,
                                          const std::string& instance_key) {
  std::string child_prefix = inst_prefix_ + std::string(inst.inst_name) + ".";
  for (ModuleItem* def : inst.resolved->function_decls) {
    if (def->method_class != port_name) continue;
    std::string tail = "." + std::string(def->name);
    auto* own = arena_.Create<std::string>(child_prefix);
    own->append(port_name).append(tail);
    RegisterRunningIn(*own, def, child_prefix, ctx_);
    if (DeclaresForkjoin(ifc, def->name)) {
      ctx_.AddForkjoinDefinition(instance_key + tail, *own);
    } else {
      RegisterRunningIn(*arena_.Create<std::string>(instance_key + tail), def,
                        child_prefix, ctx_);
    }
  }
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
  if (!port || !port->is_interface_port) return false;
  const Expr* instance = nullptr;
  const RtlirModule* ifc =
      ConnectedInterface(*port, binding.connection, instance);
  if (ifc == nullptr) return false;

  std::string port_key = inst_prefix_ + std::string(inst.inst_name) + "." +
                         std::string(binding.port_name);
  std::string instance_key = ConnectedInstanceKey(instance->text);
  BindPortToInstance(port_key, instance_key, ctx_, arena_);
  RegisterExportedSubroutines(inst, binding.port_name, ifc, instance_key);
  RegisterModportExpressions(*port, binding.connection, ifc, port_key,
                             instance_key);
  std::string port_prefix = port_key + ".";
  std::string conn_prefix = inst_prefix_ + std::string(instance->text) + ".";
  AliasVariableMembers(ifc, port_prefix, conn_prefix, ctx_, arena_);
  // A net shares one storage between its net-map entry (driver resolution)
  // and its variable-map entry (value reads). Alias both, like LowerAliases,
  // so a continuous assign driven through the port reaches the shared net and
  // the value is observable on the connected interface instance.
  auto alias_net = [&](std::string_view name) {
    auto* alias = arena_.Create<std::string>(port_prefix + std::string(name));
    std::string target = conn_prefix + std::string(name);
    ctx_.AliasNet(*alias, target);
    ctx_.AliasVariable(*alias, target);
  };
  for (const auto& net : ifc->nets) alias_net(net.name);
  // The interface's own ports are members too, the `clk` of
  // `interface bus(input logic clk)` among them, whether §23.2.2.3 makes the
  // port a net or a variable.
  for (const RtlirPort& ifc_port : ifc->ports) alias_net(ifc_port.name);
  // §25.5.5 (printed pages 791-792): the interface's clocking blocks are its
  // members too, reached through the port as `b1.sb` is from the program the
  // port is declared in, so each block, and the event variable §14.10 names by
  // it, answers to the port's name for it.
  for (const ModuleItem* cb : ifc->clocking_blocks) {
    if (cb->name.empty()) continue;
    auto* alias =
        arena_.Create<std::string>(port_prefix + std::string(cb->name));
    std::string target = conn_prefix + std::string(cb->name);
    ctx_.AcquireClockingManager().AddBlockAlias(*alias, target);
    ctx_.AliasVariable(*alias, target);
  }
  return true;
}

// §32.4.4: a hierarchical name the way an SDF file writes it. The design spells
// a path with `.` and SDF spells it with `/`, and the annotator matched the
// entry's names against the second spelling (CollectInterconnectTopology in
// src/simulator/specify_interconnect.cpp), so a name handed to it has to be in
// that spelling too.
static std::string SdfHierName(const std::string& dotted) {
  std::string out = dotted;
  for (char& c : out) {
    if (c == '.') c = '/';
  }
  return out;
}

// The two halves of one §23.3.2 input port connection, as §32.4.4 names them:
// the instance's port, which is the load an interconnect delay is annotated
// onto, and the signal the parent connected to it, which is the source it is
// annotated from. Bundled because they are the four things one such name is
// built out of and the assignment they are written onto is a fifth.
struct PortConnectionPath {
  const std::string& inst_prefix;
  const std::string& inst_seg;
  std::string_view port_name;
  const Expr* connection;
};

// §32.4.4: names the load and the source of one input port connection on the
// assignment that carries it, so the run can ask what was annotated between
// them. A connection that is not a plain signal name leaves the source unnamed,
// which still reads a PORT or NETDELAY delay, those being the delay from every
// source on the net.
static void NameInterconnectPath(const PortConnectionPath& path,
                                 RtlirContAssign& ca) {
  ca.interconnect_load = SdfHierName(path.inst_prefix + path.inst_seg +
                                     std::string(path.port_name));
  if (path.connection == nullptr ||
      path.connection->kind != ExprKind::kIdentifier) {
    return;
  }
  ca.interconnect_source =
      SdfHierName(path.inst_prefix + std::string(path.connection->text));
}

// One unpacked dimension's addresses: the smaller bound, how many there are,
// and whether the left bound is the larger.
struct UnpackedDimShape {
  int64_t lo = 0;
  uint32_t size = 0;
  bool descending = false;

  // The address `position` elements from the dimension's left bound.
  [[nodiscard]] int64_t AddressAt(uint32_t position) const {
    return descending ? lo + size - 1 - position : lo + position;
  }
};

// The dimension of an array a connection names: a whole array's first, or,
// for a select of it, `arr[k]` of `int arr[3][3]`, the one the select leaves.
// False where the connection names no array with that many dimensions.
static bool ConnectionDimShape(const Expr* conn, SimContext& ctx, Arena& arena,
                               UnpackedDimShape& out) {
  size_t depth = 0;
  const Expr* root = conn;
  while (root->kind == ExprKind::kSelect && root->base != nullptr &&
         root->index_end == nullptr) {
    root = root->base;
    ++depth;
  }
  std::string_view key = ArrayRootKey(root, arena);
  const ArrayInfo* info = key.empty() ? nullptr : ctx.FindArrayInfo(key);
  if (info == nullptr || info->is_dynamic || info->is_queue) return false;
  if (info->dim_sizes.empty()) {
    out = {info->lo, info->size, info->is_descending};
    return depth == 0;
  }
  if (depth >= info->dim_sizes.size()) return false;
  out = {info->dim_los[depth], info->dim_sizes[depth],
         depth < info->dim_descending.size() && info->dim_descending[depth]};
  return true;
}

static Expr* MakeElementSelect(Expr* base, int64_t address, Arena& arena) {
  auto* index = arena.Create<Expr>();
  index->kind = ExprKind::kIntegerLiteral;
  index->int_val = static_cast<uint64_t>(address);
  auto* select = arena.Create<Expr>();
  select->kind = ExprKind::kSelect;
  select->base = base;
  select->index = index;
  return select;
}

// An inout or ref array port and the array it is connected to, element by
// element, left index to left index.
struct ArrayPortAlias {
  std::string local;
  std::string target;
  UnpackedDimShape port_shape;
  UnpackedDimShape conn_shape;
};

// §23.3.3.3 and §23.3.3.2 make an inout or a ref port one object with its
// connection, as LowerPortBindings aliases a scalar one; an array port is so
// element by element.
static void AliasArrayPortElements(const ArrayPortAlias& a, SimContext& ctx,
                                   Arena& arena) {
  for (uint32_t p = 0; p < a.port_shape.size; ++p) {
    const std::string& local_key = *arena.Create<std::string>(
        a.local + "[" + std::to_string(a.port_shape.AddressAt(p)) + "]");
    std::string target =
        a.target + "[" + std::to_string(a.conn_shape.AddressAt(p)) + "]";
    ctx.AliasVariable(local_key, target);
    ctx.AliasNet(local_key, target);
  }
}

// §23.3.3.5 (printed page 748): an unpacked array port connected to an
// unpacked array has "each element of the port connection ... matched to the
// port left index to left index, right index to right index", and each pair
// is connected as a port of the element's type would be: an input's element
// takes the connection's continuously, an output's drives it, and an inout's
// or ref's is the same storage. `input var int i[3]` on `int one[3]` reads
// one[0] to one[2] in i[0] to i[2]; the whole array was lowered as one
// assignment of an element's width, so the port read one value's bits. False
// for a port that is no one-dimensional unpacked array, or a connection that
// names no array of as many elements, which keep the scalar path.
// §27.4: a port connection written in a loop generate block may read the
// block's implicit localparam, and a name it reads may be one the block
// declares, so the assignment a connection is lowered to carries the loop
// constants and generate prefixes of the block instance holding the instance,
// which Lowerer::LowerContAssign binds while evaluating it.
static RtlirContAssign PortBindingAssign(const RtlirModuleInst& inst) {
  RtlirContAssign ca;
  ca.gen_block_consts = inst.gen_block_consts;
  ca.gen_block_prefixes = inst.gen_block_prefixes;
  return ca;
}

bool Lowerer::LowerArrayPortBinding(const RtlirModuleInst& inst,
                                    const RtlirPortBinding& binding,
                                    const std::string& inst_seg,
                                    bool from_program) {
  const RtlirPort* port = FindChildPort(inst, binding.port_name);
  if (port == nullptr || port->num_unpacked_dims != 1 ||
      port->unpacked_dims.size() != 1) {
    return false;
  }
  const RtlirUnpackedDim& dim = port->unpacked_dims.front();
  UnpackedDimShape port_shape{dim.Low(), dim.Size(), dim.left > dim.right};
  UnpackedDimShape conn_shape;
  if (!ConnectionDimShape(binding.connection, ctx_, arena_, conn_shape) ||
      conn_shape.size != port_shape.size) {
    return false;
  }
  std::string local = inst_seg + std::string(binding.port_name);
  if (binding.direction == Direction::kInout ||
      binding.direction == Direction::kRef) {
    // Only a connection naming the array itself is aliased, as a scalar
    // inout's is.
    if (binding.connection->kind == ExprKind::kIdentifier) {
      AliasArrayPortElements(
          {inst_prefix_ + local,
           inst_prefix_ + std::string(binding.connection->text), port_shape,
           conn_shape},
          ctx_, arena_);
    }
    return true;
  }
  bool input = binding.direction == Direction::kInput;
  for (uint32_t p = 0; p < port_shape.size; ++p) {
    Expr* local_elem = MakeElementSelect(MakeLocalPortId(local, arena_),
                                         port_shape.AddressAt(p), arena_);
    Expr* conn_elem =
        MakeElementSelect(binding.connection, conn_shape.AddressAt(p), arena_);
    RtlirContAssign ca = PortBindingAssign(inst);
    ca.lhs = input ? local_elem : conn_elem;
    ca.rhs = input ? conn_elem : local_elem;
    ca.width = port->width;
    LowerContAssign(ca, from_program);
  }
  return true;
}

// What an inout or ref port binding of one instance is joined in: the
// instance's segment and its parent's prefix, and the connection each of the
// instance's objects was joined to first.
struct InoutJoinScope {
  SimContext& ctx;
  Arena& arena;
  std::string local_prefix;
  const std::string& parent_prefix;
  std::unordered_map<std::string_view, std::string_view>& joins;
};

// §23.3.3.2 ref ports and §23.3.3.3 inout ports both share storage with the
// connected parent signal, so the child port is aliased onto it rather than
// lowered as a one-way continuous assignment. An inout port is a net
// (§23.3.3.3 connects it to a net and never to a variable), and §23.3.3.7
// merges the port's net and the connected net into one simulated net, so the
// net map is redirected beside the variable map, as LowerAliases and
// TryAliasInterfacePort do: a continuous assignment inside the child resolves
// its driver through SimContext::FindNet under the child's prefix, where
// CreatePortVariable (lowerer_register.cpp) registered the port's own net,
// and with the variable alone aliased that net took the driver and the
// parent's net never saw it. A ref port's connection is a variable, which
// FindNet does not answer, so its net alias is a no-op. The keys are interned
// in the arena because the net map holds them rather than a copy.
//
// §23.2.2.1 (printed page 732), Example 4: `same_port (.a(i), .b(i))` has two
// ports on the one inout i, so the two connections are one net with i. The
// first is joined to i; a later one joins the first.
static void JoinInoutPortBinding(const RtlirPortBinding& binding,
                                 const InoutJoinScope& scope) {
  if (binding.connection->kind != ExprKind::kIdentifier) return;
  const std::string& local = *scope.arena.Create<std::string>(
      scope.local_prefix + std::string(PortStorageName(binding)));
  const std::string& target = *scope.arena.Create<std::string>(
      scope.parent_prefix + std::string(binding.connection->text));
  auto [joined, fresh] = scope.joins.try_emplace(local, target);
  if (!fresh) {
    scope.ctx.AliasVariable(target, joined->second);
    scope.ctx.AliasNet(target, joined->second);
    return;
  }
  scope.ctx.AliasVariable(local, target);
  scope.ctx.AliasNet(local, target);
}

// §16.18 with §17.3: an input formal of a checker bound to a clocking block
// variable, `cb.a`, stands for that variable in the checker's assertions,
// which read what the block sampled rather than a sample of the formal; the
// block is found by its name in the instance holding the checker when read.
static void BindCheckerClockvarFormal(const RtlirModuleInst& inst,
                                      const RtlirPortBinding& binding,
                                      const std::string& parent_prefix,
                                      const std::string& formal_name,
                                      SimContext& ctx) {
  const Expr* actual = binding.connection;
  if (inst.resolved == nullptr || !inst.resolved->is_checker ||
      actual->kind != ExprKind::kMemberAccess || actual->is_scope_resolution ||
      actual->lhs->kind != ExprKind::kIdentifier) {
    return;
  }
  ctx.AcquireClockingManager().BindCheckerFormal(
      ctx.FindVariable(formal_name),
      parent_prefix + std::string(actual->lhs->text),
      std::string(actual->rhs->text));
}

// §6.16: the width the connection to an input port is evaluated and written
// at, the port's own, or none for a string port, which holds as many
// characters as its connection gives it.
static uint32_t InputPortAssignWidth(const RtlirPortBinding& binding,
                                     const std::string& port_name,
                                     SimContext& ctx) {
  return ctx.IsStringVariable(port_name) ? 0 : binding.width;
}

// The port side of `binding`, qualified with the instance's segment: its port
// expression where the header wrote one, else the port's own name.
static Expr* LocalPortExpr(const RtlirPortBinding& binding,
                           const std::string& inst_seg, Arena& arena) {
  if (binding.port_expr != nullptr) {
    return QualifiedPortExpr(binding.port_expr, inst_seg, arena);
  }
  return MakeLocalPortId(inst_seg + std::string(binding.port_name), arena);
}

// §17.3: the actuals a checker instance binds to its formals, registered under
// the instance for its assertions to take a delay bound written as a formal's
// name, an event, a sequence or a property from, each of the last three
// reading its names in `parent_prefix`, the scope instantiating the checker.
static void RecordCheckerActuals(const RtlirModuleInst& inst,
                                 const std::string& parent_prefix,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena) {
  if (!inst.resolved->is_checker) return;
  ActualsByFormal actuals;
  for (const RtlirPortBinding& binding : inst.port_bindings) {
    actuals[binding.port_name] =
        ActualInInstantiatingScope(binding.connection, parent_prefix, arena);
  }
  ctx.RegisterCheckerActuals(inst_prefix, std::move(actuals));
}

const std::vector<EventExpr>& Lowerer::ClockOf(const RtlirProcess& proc) {
  if (!lowering_checker_) return proc.sensitivity;
  return *arena_.Create<std::vector<EventExpr>>(SubstituteClock(
      proc.sensitivity, CheckerTreeActuals(inst_prefix_, ctx_), arena_));
}

// §16.5.1 with §17.3: the variables a checker's sequence or property actual
// reads are read sampled in the checker's assertions, as they are where the
// actual is written, so they are enrolled under the instantiating scope.
void Lowerer::RecordCheckerActualSampleScope(const RtlirModuleInst& inst) {
  std::unordered_set<std::string> names;
  for (const RtlirPortBinding& binding : inst.port_bindings) {
    CollectActualReadNames(binding.connection, names);
  }
  if (names.empty()) return;
  AssertionSampleScope scope;
  scope.inst_prefix = inst_prefix_;
  scope.names.assign(names.begin(), names.end());
  assertion_sample_scopes_.push_back(std::move(scope));
}

void Lowerer::LowerPortBindings(const RtlirModuleInst& inst,
                                bool from_program) {
  // §23.3.2: the caller lowers bindings under the PARENT prefix; qualify the
  // port (local) side with the child segment ("u0.a") so the connection side
  // stays bare and resolves in the parent. Otherwise an implicit/wildcard
  // connection (.a == .a(a)) resolves to the child's own same-named port and
  // self-assigns instead of propagating.
  std::string inst_seg = std::string(inst.inst_name) + ".";
  RecordCheckerActuals(inst, inst_prefix_, inst_prefix_ + inst_seg, ctx_,
                       arena_);
  RecordCheckerActualSampleScope(inst);
  RecordProceduralCheckerActuals(inst, inst_prefix_ + inst_seg);
  std::unordered_map<std::string_view, std::string_view> inout_joins;
  for (const auto& binding : inst.port_bindings) {
    if (TryAliasInterfacePort(inst, binding)) continue;
    if (!IsConnectablePortBinding(inst, binding)) continue;
    if (LowerArrayPortBinding(inst, binding, inst_seg, from_program)) continue;

    Expr* local_id = LocalPortExpr(binding, inst_seg, arena_);

    // An inout or ref port shares its connection's storage
    // (JoinInoutPortBinding), and so does an event port, whose connection is
    // triggered rather than assigned (§15.5).
    if (binding.direction == Direction::kInout ||
        binding.direction == Direction::kRef ||
        BoundPortType(inst, binding) == DataTypeKind::kEvent) {
      JoinInoutPortBinding(binding, {ctx_, arena_, inst_prefix_ + inst_seg,
                                     inst_prefix_, inout_joins});
      continue;
    }

    if (binding.direction == Direction::kInput) {
      std::string port_name =
          inst_prefix_ + inst_seg + std::string(binding.port_name);
      BindCheckerClockvarFormal(inst, binding, inst_prefix_, port_name, ctx_);
      RtlirContAssign ca = PortBindingAssign(inst);
      ca.lhs = local_id;
      ca.rhs = binding.connection;
      ca.width = InputPortAssignWidth(binding, port_name, ctx_);
      // §32.4.4: this assignment is the path an interconnect delay is annotated
      // along -- from the signal the parent connected to the port of the
      // instance -- so it carries the two names the annotator placed the delay
      // between.
      NameInterconnectPath(
          {inst_prefix_, inst_seg, binding.port_name, binding.connection}, ca);
      LowerContAssign(ca, from_program);
      continue;
    }

    // The output drives its connection; besides a bare net this may be a
    // part-select, element select, or concatenation produced by §23.3.3.5
    // instance-array distribution, all of which the continuous-assignment
    // lvalue writer now handles.
    if (!IsDrivableOutputConnection(binding.connection->kind)) continue;
    RtlirContAssign ca = PortBindingAssign(inst);
    ca.lhs = binding.connection;
    ca.rhs = local_id;
    ca.width = binding.width;
    ca.module_path_port =
        inst_prefix_ + inst_seg + std::string(binding.port_name);
    path_delayed_ports_.insert(ca.module_path_port);
    LowerContAssign(ca, from_program);
  }
}

}  // namespace delta
