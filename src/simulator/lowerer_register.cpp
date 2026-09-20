#include "simulator/lowerer_register.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

namespace delta {

void RecordPackedRange(const DataType* dt, Variable* v, SimContext& ctx,
                       Arena& arena) {
  if (!dt || !dt->packed_dim_left || !dt->packed_dim_right) return;
  auto eval = [&](const Expr* e) {
    return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
  };
  auto span = [](int64_t l, int64_t r) {
    return static_cast<uint64_t>((l >= r ? l - r : r - l) + 1);
  };
  uint64_t stride = 1;
  for (const auto& [l, r] : dt->extra_packed_dims)
    stride *= span(eval(l), eval(r));
  if (stride > 1) v->packed_elem_width = static_cast<uint32_t>(stride);
  PackedRange range{eval(dt->packed_dim_left), eval(dt->packed_dim_right)};
  // The elaborator sized this storage from the same dimensions. Bounds that do
  // not account for its width came from an expression this scope cannot fold,
  // and a range read off them would misaddress every bit, so leave the storage
  // addressed as [width-1:0].
  if (span(range.left, range.right) * stride != v->value.width) return;
  v->packed_range = range;
  v->has_packed_range = true;
}

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena) {
  for (const auto& net : mod->nets) {
    auto* created = ctx.CreateNet(
        net.name, net.net_type, net.width,
        NetSpec{net.charge_strength, net.decay_ticks, net.decays,
                net.is_user_nettype, net.resolve_func, net.is_signed});
    RecordPackedRange(net.dtype, created->resolved, ctx, arena);
  }
}

// §23.3.3.2: an input port "shall have the default initial value corresponding
// to the data type" when left unconnected, and Table 6-7 gives that value per
// type. Fresh storage is created holding x, which is already the 4-state
// integral default, so only a type whose default is zero needs writing. String
// and event are excluded for the same reason the body declaration excludes
// them: their defaults are an empty string and a new event, neither of which
// is a bit pattern this write would produce.
bool PortDefaultsToZero(const RtlirPort& port) {
  if (port.type_kind == DataTypeKind::kString ||
      port.type_kind == DataTypeKind::kEvent) {
    return false;
  }
  return !Is4stateType(port.type_kind);
}

void CreatePortVariable(std::string_view name, const RtlirPort& port,
                        SimContext& ctx, Arena& arena) {
  // §21.7.4.3.1: an extended VCD port record takes its state characters from
  // the list for the port's direction, and the direction is a property of the
  // declaration rather than of the storage. Recorded before the question below
  // of whether storage already exists, because a port whose name a module-body
  // declaration already created is still a port and still faces one way.
  ctx.Vcd().SetVcdPortDirection(name, port.direction);
  if (ctx.FindVariable(name)) return;
  // §23.2.2.3 decides whether a port is a net or a variable, and a port it
  // makes a net is one: its drivers resolve against each other (§28.12) and it
  // carries a strength, which is what %v (§21.2.1.4) and an extended VCD port
  // record (§21.7.4.3) report. Where the port is written -- in the header or,
  // as a net declaration, in the body -- decides nothing, so the two spellings
  // reach the same model.
  Variable* v = nullptr;
  if (port.net_type != NetType::kNone) {
    v = ctx.CreateNet(name, port.net_type, port.width,
                      NetSpec{.is_signed = port.is_signed})
            ->resolved;
    // §23.3.3.2 with Table 6-7 gives a port its data type's default initial
    // value, and that is the port's own rule: §6.7.1's undriven-net z, which
    // CreateNet has just installed, belongs to a net no port declaration
    // named. Putting the port's default back is what keeps a net-kind port
    // reading what it read before it was one.
    // §6.8, Table 6-7: an uninitialized 4-state integral object is 'x, which
    // SimContext::CreateVariable installed and CreateNet then replaced with
    // §6.7.1's undriven-net z. The storage is the width CreateNet was given,
    // so FillWithX writes the same bits back that CreateVariable wrote.
    FillWithX(v->value);
  } else {
    v = ctx.CreateVariable(name, port.width);
  }
  // §23.3.3.2, Table 6-7: an unconnected input reads as its type's default
  // rather than as whatever the storage happens to hold. A 4-state type's
  // default is the x both branches above leave behind; only a 2-state one
  // needs writing.
  if (PortDefaultsToZero(port))
    v->value = MakeLogic4VecVal(arena, port.width, 0);
  // §23.2.2.2, footnote 2: a variable output port may be initialized, and its
  // `= constant_expression` is the value it holds before any procedure runs,
  // as §6.8 gives a variable declaration's initializer. The value is sized to
  // the port as an assignment to it would be (§10.7), and a 2-state port takes
  // it through §6.11.2's conversion as any variable's initializer does.
  if (port.init_value != nullptr) {
    Logic4Vec init = OwnRhsWords(
        ResizeToWidth(EvalExpr(port.init_value, ctx, arena, port.width),
                      port.width, arena),
        arena);
    if (PortDefaultsToZero(port)) CoerceTo2State(init);
    v->value = init;
  }
  if (port.is_signed) v->is_signed = true;
  // §11.5.1: "The actual bit that is accessed by an address is, in part,
  // determined by the declaration" -- port.width says how many bits the port
  // has rather than which bit an index names, because `[8:1]` and `[1:8]` are
  // both eight bits wide and index 3 reaches a different bit of each.
  RecordPackedRange(port.dtype, v, ctx, arena);
  // §21.7.5 (Table 21-11): a port declared with a SystemVerilog data type is
  // dumped under that type's 1364-2005 masquerade, just as a module-body
  // declaration of the same type is. A port reaching here has no body
  // declaration that already recorded its kind, so record the declared keyword
  // now. The port carries only that keyword, so an enum port keeps the default
  // enum mapping rather than any specified base type.
  ctx.Vcd().SetVcdVarKind(name, port.type_kind);
}

void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx,
                         Arena& arena) {
  for (const auto& port : mod->ports) {
    CreatePortVariable(port.name, port, ctx, arena);
  }
}

void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx) {
  for (auto* func : mod->function_decls) {
    // §8.24: an out-of-block method body among the module's items is a
    // method of the class its `C::` prefix names, which LowerClassDecl
    // attaches, and not a subroutine of the module under its bare name.
    if (!func->method_class.empty()) continue;
    ctx.RegisterFunction(func->name, func);
  }
  for (auto* let_decl : mod->let_decls) {
    ctx.RegisterLetDecl(let_decl->name, let_decl);
  }
}

// §26.3: a package's subroutine is referenced through the package scope
// resolution operator, `pk::f(x)`, from any scope, imported or not, so each
// one is registered under its "pk::f" key, the key a scoped call resolves by
// (SubroutineKey in eval_function.cpp). An import binds the bare name as
// well, in LowerPackageItem. §8.24 keeps an out-of-block method body out of
// the package's own subroutines.
void RegisterPackageScopedSubroutines(const RtlirDesign* design,
                                      SimContext& ctx, Arena& arena) {
  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items) {
      // §26.3 with §13.4: the package's subroutines read its variables, and
      // through its imports another package's, by their bare names, so each
      // subroutine is recorded as the package's and each import as one of
      // the package's; SimContext::FindInPackageScope reads both back.
      if (item->kind == ModuleItemKind::kImportDecl) {
        const ImportItem& imp = item->import_item;
        ctx.RegisterPackageImport(pkg->name, imp.package_name,
                                  imp.is_wildcard ? "*" : imp.item_name);
        continue;
      }
      bool is_subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                           item->kind == ModuleItemKind::kTaskDecl;
      if (!is_subroutine || !item->method_class.empty()) continue;
      ctx.RegisterSubroutinePackage(item, pkg->name);
      auto* key = arena.Create<std::string>(std::string(pkg->name) +
                                            "::" + std::string(item->name));
      ctx.RegisterFunction(*key, item);
    }
  }
}

// The default a package variable with no initializer holds: §6.8's Table 6-7
// gives a 4-state integral variable x, which CreateVariable filled, and a
// 2-state one 0. A string and a real are registered as such, since a read of
// either goes through the kind rather than through the bits.
static void ShapePackageVariable(const ModuleItem* item, Variable* var,
                                 std::string_view qname, SimContext& ctx,
                                 Arena& arena) {
  const DataType& type = item->data_type;
  var->is_4state = DeclaredTypeIs4State(type);
  var->is_signed = DeclaredTypeIsSigned(type, ctx);
  var->value.is_signed = var->is_signed;
  if (!var->is_4state)
    var->value = MakeLogic4VecVal(arena, var->value.width, 0);
  if (DeclaredTypeIsString(type, ctx)) ctx.RegisterStringVariable(qname);
  bool is_real = type.kind == DataTypeKind::kReal ||
                 type.kind == DataTypeKind::kShortreal ||
                 type.kind == DataTypeKind::kRealtime;
  if (is_real) ctx.RegisterRealVariable(qname);
}

void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena) {
  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items) {
      bool is_param = item->kind == ModuleItemKind::kParamDecl;
      bool is_var = item->kind == ModuleItemKind::kVarDecl;
      if (!(is_var || (is_param && item->init_expr))) continue;
      auto* qname = arena.Create<std::string>(std::string(pkg->name) + "." +
                                              std::string(item->name));
      uint32_t width = is_var ? DeclaredTypeWidth(item->data_type, ctx) : 0;
      auto* var = ctx.CreateVariable(*qname, width == 0 ? 32 : width);
      if (is_var) ShapePackageVariable(item, var, *qname, ctx, arena);
      if (item->init_expr) var->value = EvalExpr(item->init_expr, ctx, arena);
    }
  }
}

// §6.19 makes an enumeration's members constants of the scope the enumeration
// is written in, and §26.3 references a package's declaration through the
// package scope resolution operator, so `pk::MED` names the package's constant
// from any scope, imported or not -- a class property's initializer, a write
// through a handle, a module's own expression. A wildcard import emits the
// literals as the importing module's variables (RegisterImportedEnumLiterals
// in elaborator_typedef.cpp) and a package parameter is created under its
// "pk.name" key (InitPackageDataVariables in lowerer.cpp), which is the key
// EvalMemberAccess reads a scoped name by; the package's enumeration constants
// alone had no storage, so `pk::MED` read 0 wherever it was written. Each is
// created under that key with its member's value, folded as the elaborator's
// RegisterPackageParams folds it: against the package's parameters and
// constants declared before it, which §6.20.1 and §6.19 let a member's value
// name, and at the width of the enumeration's base type.
void RegisterPackageEnumConstants(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena) {
  for (auto* pkg : design->packages) {
    ScopeMap values;
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
        if (auto v = ConstEvalInt(item->init_expr, values))
          values[item->name] = *v;
        continue;
      }
      // Syntax 6-5 lets the enumeration stand as the type a typedef names or
      // as the type of a data declaration, and the constants are the same.
      auto members = BindEnumConstantsOfItem(item, values, arena);
      if (members.empty()) continue;
      const DataType& type = item->kind == ModuleItemKind::kTypedef
                                 ? item->typedef_type
                                 : item->data_type;
      uint32_t width = EvalTypeWidth(type, {});
      if (width == 0) width = 32;
      for (const auto& m : members) {
        auto* qname = arena.Create<std::string>(std::string(pkg->name) + "." +
                                                std::string(m.name));
        auto* var = ctx.CreateVariable(*qname, width);
        var->value =
            MakeLogic4VecVal(arena, width, static_cast<uint64_t>(m.value));
      }
    }
  }
}

// §35.5.4 declares an imported subroutine in the scope that writes the
// declaration, and §35.6 has a call to one written exactly as a call to a
// native subroutine. The registry is what a call reaches the declaration
// through, so a design's declarations are put in it as the design is lowered;
// a design that declares no import never asks for one. The registry holds one
// entry per SystemVerilog name, and a module instantiated twice registers its
// declarations once: the second instance's are the same declarations.
static void RegisterDpiImportDecls(const std::vector<ModuleItem*>& decls,
                                   SimContext& ctx) {
  DpiRuntime* dpi = nullptr;
  for (const auto* item : decls) {
    if (item->kind != ModuleItemKind::kDpiImport) continue;
    if (dpi == nullptr) dpi = &ctx.AcquireDpiRuntime();
    if (dpi->HasImport(item->name)) continue;
    DpiRtFunction func;
    func.sv_name = item->name;
    // §35.4: "If a global name is not explicitly given, it shall be the same as
    // the SystemVerilog subroutine name", which is the rule
    // DpiLinkageName states for the elaborator's own reading of the same
    // declaration.
    func.c_name = item->dpi_c_name.empty() ? item->name : item->dpi_c_name;
    func.return_type = item->return_type.kind;
    // §35.5.1.3: the declaration says whether the subroutine is pure or
    // context, and §35.5.2 and §35.5.3 are read off those two.
    func.is_pure = item->dpi_is_pure;
    func.is_context = item->dpi_is_context;
    // §H.2: an import declares a task or a function, and only an imported task
    // can in turn call exported tasks.
    func.is_task = item->dpi_is_task;
    // §H.14.1: a declaration annotated "DPI" selects the SV3.1a argument
    // passing semantics on the C side and one annotated "DPI-C" the IEEE Std
    // 1800 semantics, per function.
    func.packed_arg_passing =
        DpiPassingSemanticsOfSpecString(item->dpi_spec_string);
    for (const auto& arg : item->func_args) {
      DpiArg formal;
      formal.name = arg.name;
      formal.type = arg.data_type.kind;
      // §35.5.1.2 reads the direction to decide which way each formal's value
      // crosses, so it travels with the declaration rather than being inferred
      // at the call.
      formal.direction = arg.direction;
      // §35.6: the default the declaration gave a formal, which a call site
      // that omits the argument takes.
      formal.default_value = arg.default_value;
      // §35.5.6 admits "Packed arrays, structs, and unions composed of types
      // bit and logic" as formal types and names no width limit, and
      // DataTypeKind says only kBit or kLogic for one of those. So the width
      // the declaration wrote travels beside the kind for exactly those types;
      // every other formal's type states its own width, and recording one for
      // it would put a second answer beside the kind's.
      if (DataTypeKind kind = arg.data_type.kind;
          kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ||
          kind == DataTypeKind::kReg) {
        formal.width = EvalTypeWidth(arg.data_type);
      }
      // §H.7.4: an integer type the declaration qualified unsigned crosses
      // as the unsigned C type; the parser has already settled the default
      // signedness of a type that named neither qualifier.
      formal.is_unsigned = !arg.data_type.is_signed;
      // §H.7.5: a struct or union crosses under the name of its type.
      formal.type_name = arg.data_type.type_name;
      func.args.push_back(formal);
    }
    dpi->RegisterImport(std::move(func));
  }
}

void RegisterModuleDpiImports(const RtlirModule* mod, SimContext& ctx) {
  RegisterDpiImportDecls(mod->dpi_import_decls, ctx);
}

// §6.18 with §8.25.1: a typedef name whose chain ends in a class names that
// class -- `typedef C T;` makes `T::p` the default specialization's `C#()::p`
// -- so each such name is bound to the class it denotes, once every class of
// the design is lowered, unless the design declares a class of that name.
void RegisterClassTypeAliases(const RtlirDesign* design, SimContext& ctx) {
  for (const auto& [alias, target] : design->type_targets) {
    if (ctx.FindClassType(alias) != nullptr) continue;
    ClassTypeInfo* cls = ctx.FindClassType(target);
    if (cls != nullptr) ctx.RegisterClassType(alias, cls);
  }
}

void RegisterDesignScopeDpiImports(const RtlirDesign* design, SimContext& ctx) {
  for (const auto* pkg : design->packages) {
    RegisterDpiImportDecls(pkg->items, ctx);
  }
  if (design->compilation_unit != nullptr) {
    RegisterDpiImportDecls(design->compilation_unit->cu_items, ctx);
  }
}

void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx) {
  for (auto* prop_decl : mod->property_decls) {
    ctx.RegisterPropertyDecl(prop_decl->name, prop_decl);
  }
  for (auto* seq_decl : mod->sequence_decls) {
    ctx.RegisterSequenceDecl(seq_decl->name, seq_decl);

    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx.FindVariable(ep_name)) {
      // variables_ keys by string_view, so the key's backing string must
      // outlive the map; intern it in the arena. A local std::string would
      // dangle and make every later FindVariable("__seq_<name>") miss.
      auto* stored = ctx.GetArena().Create<std::string>(std::move(ep_name));
      auto* ep_var = ctx.CreateVariable(*stored, 1);
      ep_var->is_event = true;
    }
  }
}

void RegisterProcessClassType(SimContext& ctx, Arena& arena) {
  auto* proc_type = arena.Create<ClassTypeInfo>();
  proc_type->name = "process";
  proc_type->enum_members["FINISHED"] = 0;
  proc_type->enum_members["RUNNING"] = 1;
  proc_type->enum_members["WAITING"] = 2;
  proc_type->enum_members["SUSPENDED"] = 3;
  proc_type->enum_members["KILLED"] = 4;
  ctx.RegisterClassType("process", proc_type);
}

}  // namespace delta
