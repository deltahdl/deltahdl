#include "simulator/lowerer_register.h"

#include <algorithm>
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
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
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
  // §7.4.4: every dimension inside the outermost is kept as declared, so a
  // select chain steps through them one index at a time (Variable::
  // PackedLevelWithin); their product alone left `z[1][0]` on a
  // `logic [1:0][1:0][7:0]` a bit of the sixteen-bit `z[1]`.
  uint64_t stride = 1;
  std::vector<PackedRange> inner;
  for (const auto& [l, r] : dt->extra_packed_dims) {
    inner.push_back({eval(l), eval(r)});
    stride *= span(inner.back().left, inner.back().right);
  }
  if (stride > 1) {
    v->packed_elem_width = static_cast<uint32_t>(stride);
    v->inner_packed_dims = std::move(inner);
  }
  PackedRange range{eval(dt->packed_dim_left), eval(dt->packed_dim_right)};
  // The elaborator sized this storage from the same dimensions. Bounds that do
  // not account for its width came from an expression this scope cannot fold,
  // and a range read off them would misaddress every bit, so leave the storage
  // addressed as [width-1:0].
  if (span(range.left, range.right) * stride != v->value.width) return;
  v->packed_range = range;
  v->has_packed_range = true;
}

// §23.9 with §23.10.2: the instance an override of `prefix`'s parameters was
// written in is the instance holding `prefix`. Its prefix is found by dropping
// one dotted component at a time until what is left names an instance
// RegisterInstanceKeyBinding (src/simulator/lowerer.cpp) recorded -- the top
// under the empty key -- because a generate block's instance,
// "u1.g[0].u2.", is keyed through the block and the block itself is no
// instance.
static std::string InstantiatingPrefix(std::string_view prefix,
                                       SimContext& ctx) {
  std::string parent(prefix);
  while (!parent.empty()) {
    parent.pop_back();
    auto dot = parent.rfind('.');
    parent =
        dot == std::string::npos ? std::string() : parent.substr(0, dot + 1);
    std::string key = parent;
    if (!key.empty()) key.pop_back();
    if (!ctx.FindInstanceType(key).empty()) break;
  }
  return parent;
}

// §6.20.2 lets a value parameter's expression name literals, parameters,
// genvars, enumeration names, constant functions and package references, and
// this is which of those have storage the instance can read now, its own
// parameters lowered ahead of it. A subroutine is registered after the
// parameters, an enumeration constant and an imported name are bound after
// them, and a genvar or a configuration's localparam has no storage at all, so
// a name FindVariable does not answer and any subroutine call say no. The
// two sides of a package scope resolution, `pk::X`, are a package's key and
// its member rather than names of this scope, and the package's storage was
// created ahead of every module, so those are passed over.
static bool EveryNameHasStorage(const Expr* expr, SimContext& ctx) {
  std::vector<const Expr*> scoped;
  ForEachSubExpr(expr, [&](const Expr* e) {
    if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution) {
      scoped.push_back(e->lhs);
      scoped.push_back(e->rhs);
    }
  });
  bool all = true;
  ForEachSubExpr(expr, [&](const Expr* e) {
    if (e->kind == ExprKind::kCall) all = false;
    if (e->kind != ExprKind::kIdentifier) return;
    if (std::find(scoped.begin(), scoped.end(), e) != scoped.end()) return;
    if (ctx.FindVariable(e->text) == nullptr) all = false;
  });
  return all;
}

void WidenParamValue(const RtlirParamDecl& param, Variable* var,
                     SimContext& ctx, Arena& arena) {
  uint32_t width = var->value.width;
  if (width <= 64) return;
  // ApplyParamOverride in src/elaborator/elaborator_module.cpp records the
  // override's expression, and Elaborator::ApplyDefparamSite a defparam's
  // literal. An override that recorded no expression -- a defparam naming
  // something, or §33.4.3's `#()` handing the declaration's own initializer
  // back -- replaced the declaration's value with one no expression here
  // spells, so that value stays as folded.
  if (param.from_override && param.override_expr == nullptr) return;
  const Expr* expr = param.override_expr != nullptr ? param.override_expr
                                                    : param.default_value;
  if (expr == nullptr) return;
  std::string own = ctx.ActiveInstancePrefix();
  if (param.override_expr != nullptr)
    ctx.SetLoweringInstancePrefix(InstantiatingPrefix(own, ctx));
  if (EveryNameHasStorage(expr, ctx)) {
    // §11.6.1 with §6.20.2: the value is sized to the declaration as an
    // assignment to it is. The words are copied because an expression that is
    // a bare parameter name answers that parameter's own storage.
    Logic4Vec value = EvalExpr(expr, ctx, arena, width);
    var->value = OwnRhsWords(ResizeToWidth(value, width, arena), arena);
  }
  ctx.SetLoweringInstancePrefix(own);
}

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena) {
  for (const auto& net : mod->nets) {
    auto* created = ctx.CreateNet(
        net.name, net.net_type, net.width,
        NetSpec{net.charge_strength, net.decay_ticks, net.decays,
                net.is_user_nettype, net.resolve_func, net.is_signed});
    RecordPackedRange(net.dtype, created->resolved, ctx, arena);
    // §6.7.1 with §7.2.1: a net of a packed structure, `wire instruction_t
    // w`, is laid out from the aggregate its declaration carries so a member
    // select names a run of the net's bits, as a net port's is.
    RegisterAggregateLayout(net.name, net.dtype, net.width, ctx, arena);
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
  // §7.2.1 with §23.2.2.3: a port the clause makes a net may be a net of a
  // packed structure (§6.7.1), and a member select of it names a run of the
  // net's bits. The elaborator hands such a port its resolved aggregate on the
  // same record field, since it declares no variable for a net; a variable
  // port of a structure never reaches here, its declaration having created
  // and laid out the storage above.
  RegisterAggregateLayout(name, port.dtype, port.width, ctx, arena);
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

// §13.3 with §23.6: a task or function of a module instance is enabled by
// its hierarchical name from another instance, `u1.tk(3)`, and §13.3.2 gives
// a static task in each instance its own storage, so every instance's
// subroutines are registered under the instance's prefixed key as well as
// the bare name RegisterModuleSubroutines records, "u1.tk" for the instance
// "u1." and "u1.u2.tk" for one nested in it, the key FindSubroutineTarget in
// eval_function_hier.cpp resolves a dotted callee by. The key is interned in
// the arena because the registry holds it rather than a copy. §8.24 keeps an
// out-of-block method body out of the instance's subroutines, as the bare
// registration does.
void RegisterInstanceSubroutines(const RtlirModule* mod,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena) {
  for (auto* func : mod->function_decls) {
    if (!func->method_class.empty()) continue;
    auto* key =
        arena.Create<std::string>(inst_prefix + std::string(func->name));
    ctx.RegisterFunction(*key, func);
  }
}

// §21.2.1.5 and §27.3: the generate block instances of a path spelled as
// the levels of a hierarchical name, a loop block's instance with its index
// in brackets, `g[0].h`; empty for an empty path.
std::string GenBlockName(const HierPath& path) {
  std::string name;
  for (const HierStep& step : path) {
    if (!name.empty()) name += '.';
    name += std::string(step.name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
  }
  return name;
}

// §27.4 with §13.4 and §23.6: a subroutine a named generate block instance
// declares is called from outside the block by the instance's hierarchical
// name, `blk[1].triple(10)` or `u1.blk[1].triple(10)`, so it is registered
// under that key, `key_prefix` and then the block path as §23.6 spells it,
// and the scope its body runs in is recorded under the same key for
// FindSubroutineTarget in eval_function_hier.cpp: the module instance
// `inst_prefix`, the block's name prefixes and its loop localparams, as the
// block's own processes carry them. The two prefixes part for a top-level
// module alone, whose instance is the empty prefix while §23.6 names it
// from a parallel hierarchy through the top's name, "m.blk[1].triple"
// (LowerModule in lowerer.cpp). §23.6 has a declaration of an unnamed block
// reachable by hierarchical name from within the block alone, and such a
// block's step has no name to spell, so it is registered under no key.
void RegisterGenBlockSubroutines(const RtlirModule* mod,
                                 const std::string& key_prefix,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena) {
  for (const RtlirGenBlockSubroutine& sub : mod->gen_block_subroutines) {
    bool unnamed = false;
    for (const HierStep& step : sub.gen_block_path)
      unnamed |= step.name.empty();
    if (unnamed) continue;
    auto* key = arena.Create<std::string>(key_prefix +
                                          GenBlockName(sub.gen_block_path) +
                                          "." + std::string(sub.decl->name));
    ctx.RegisterFunction(*key, sub.decl);
    GenBlockSubroutineScope scope;
    scope.inst_prefix = inst_prefix;
    scope.gen_prefixes.assign(sub.gen_block_prefixes.begin(),
                              sub.gen_block_prefixes.end());
    scope.consts = sub.gen_block_consts;
    ctx.RegisterGenBlockSubroutineScope(*key, std::move(scope));
  }
}

// §26.3: a package's subroutine is referenced through the package scope
// resolution operator, `pk::f(x)`, from any scope, imported or not, so each
// one is registered under its "pk::f" key, the key a scoped call resolves by
// (FindSubroutineTarget in eval_function_hier.cpp). An import binds the bare
// name as well, in LowerPackageItem. §8.24 keeps an out-of-block method body
// out of the package's own subroutines.
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
static void RegisterPackageItemEnumConstants(const ModuleItem* item,
                                             std::string_view pkg_name,
                                             ScopeMap& values, SimContext& ctx,
                                             Arena& arena) {
  if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
    if (auto v = ConstEvalInt(item->init_expr, values)) values[item->name] = *v;
    return;
  }
  // Syntax 6-5 lets the enumeration stand as the type a typedef names or as
  // the type of a data declaration, and §7.2 as the type of a member of a
  // structure or union either writes, which §23.9 makes no scope of its own;
  // the constants are the package's in each case, and each enumeration is
  // numbered on its own at the width of its own base type.
  ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
    uint32_t width = EvalTypeWidth(type, {});
    if (width == 0) width = 32;
    for (const auto& m : FoldEnumMembers(type.enum_members, values, arena)) {
      values[m.name] = m.value;
      auto* qname = arena.Create<std::string>(std::string(pkg_name) + "." +
                                              std::string(m.name));
      auto* var = ctx.CreateVariable(*qname, width);
      var->value =
          MakeLogic4VecVal(arena, width, static_cast<uint64_t>(m.value));
    }
  });
}

void RegisterPackageEnumConstants(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena) {
  for (auto* pkg : design->packages) {
    ScopeMap values;
    for (auto* item : pkg->items)
      RegisterPackageItemEnumConstants(item, pkg->name, values, ctx, arena);
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
