#include "simulator/lowerer_register.h"

#include <algorithm>
#include <cstddef>
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
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/eval_function_internal.h"
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

// §6.9.1: either bound of a packed dimension may be negative, so each is read
// as the integer it stands for (SelectBoundValue) and not as the magnitude of
// its bits: `logic [-1:4] b` read its `-1` as 4294967295, a span that did not
// account for the six bits, and the vector stayed addressed as [5:0], where
// b[4] was bit 4 and b[-1] out of range.
void RecordPackedRange(const DataType* dt, Variable* v, SimContext& ctx,
                       Arena& arena) {
  if (!dt || !dt->packed_dim_left || !dt->packed_dim_right) return;
  auto eval = [&](const Expr* e) {
    return SelectBoundValue(EvalExpr(e, ctx, arena));
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

// §5.7.1 (printed page 78): whether `expr` holds a literal with an x or a z
// in it -- `'x`, `'z`, or a based literal with an x, z or ? digit after its
// base -- which the elaborator's fold, holding no unknown bit, folded as 0.
static bool HoldsXZLiteral(const Expr* expr) {
  bool found = false;
  ForEachSubExpr(expr, [&](const Expr* e) {
    if (e->kind != ExprKind::kUnbasedUnsizedLiteral &&
        e->kind != ExprKind::kIntegerLiteral)
      return;
    std::string_view text = e->text;
    auto tick = text.find('\'');
    if (tick == std::string_view::npos) return;
    if (text.find_first_of("xXzZ?", tick + 1) != std::string_view::npos)
      found = true;
  });
  return found;
}

// Lowerer::LowerParams (lowerer.cpp) read decl_width wherever it was not 0
// and took 32 bits otherwise, which sized every untyped parameter to 32
// whatever its literal said, `$bits(p1)` answering 32 for `parameter p1 =
// 13'h7e`, and a bare `signed` to the one bit EvalTypeWidth gives the
// implicit type.
ParamStorageShape ParamStorageShapeOf(const RtlirParamDecl& param) {
  bool declared = param.has_decl_range ||
                  (param.has_decl_type && !param.decl_type_implicit);
  if (declared && param.decl_width > 0)
    return {param.decl_width, param.decl_is_signed};
  if (!declared && param.value_width > 0)
    return {param.value_width, param.value_is_signed || param.decl_is_signed};
  return {32, param.decl_is_signed};
}

void ReevaluateParamValue(const RtlirParamDecl& param, Variable* var,
                          SimContext& ctx, Arena& arena) {
  uint32_t width = var->value.width;
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
  if (width <= 64 && !HoldsXZLiteral(expr)) return;
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
    if (auto v =
            FoldDeclaredParamValue(item->init_expr, item->data_type, values))
      values[item->name] = *v;
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

// §6.18 with §15.4.9 (printed page 377): each typedef item among `items`,
// the type it was declared with recorded under `prefix` plus its name
// (SimContext::RegisterTypeDeclaration) -- the parameter list of a `typedef
// mailbox #(int) mb_t` stands on this type and on no name the targets hold.
// The items are the parser's and outlive the run, as a class declaration
// does.
static void RegisterTypedefItems(const std::vector<ModuleItem*>& items,
                                 std::string_view prefix, SimContext& ctx) {
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    std::string_view key = item->name;
    if (!prefix.empty()) {
      key = *ctx.GetArena().Create<std::string>(std::string(prefix) +
                                                "::" + std::string(item->name));
    }
    ctx.RegisterTypeDeclaration(key, &item->typedef_type);
  }
}

static void RegisterScopeTypedefs(const std::vector<ModuleDecl*>& decls,
                                  SimContext& ctx) {
  for (const ModuleDecl* decl : decls)
    RegisterTypedefItems(decl->items, {}, ctx);
}

// The typedef items of every scope of the design: a package's under
// "pkg::name" (§26.3), as the elaborator keys its typedef table, and a
// module's, an interface's, a program's and the compilation unit's under the
// bare name, as the type targets are keyed. A design built with no parsed
// unit behind it records none.
static void RegisterTypeDeclarations(const RtlirDesign* design,
                                     SimContext& ctx) {
  const CompilationUnit* unit = design->compilation_unit;
  if (unit == nullptr) return;
  RegisterTypedefItems(unit->cu_items, {}, ctx);
  for (const PackageDecl* pkg : unit->packages)
    RegisterTypedefItems(pkg->items, pkg->name, ctx);
  RegisterScopeTypedefs(unit->modules, ctx);
  RegisterScopeTypedefs(unit->interfaces, ctx);
  RegisterScopeTypedefs(unit->programs, ctx);
}

// §6.18 (printed page 118 of IEEE 1800-2023): the name at the end of each
// typedef name's chain, recorded for the run, class or not
// (SimContext::RegisterTypeTarget), with the typedef items' own types beside
// it (RegisterTypeDeclarations) for the parameter list a typedef of a
// parameterized mailbox carries. §15.4.9 (printed 377) declares a mailbox
// through `typedef mailbox #(string) s_mbox` and §15.3.1 (printed 373) a
// semaphore alike, neither built-in class has a record to bind the name to,
// and a class property declared through the typedef is told to be one by
// SyncKindOfType (eval_class_sync.cpp) following the chain in this table;
// with no table, `mb_t mb = new` built no mailbox. Recorded ahead of every
// class (Lowerer::LowerDesignData), since §8.9 (printed 186) with §6.21
// (printed 132-133) creates a static property's one copy at the class's
// static initialization, which lowering the class runs
// (InitStaticProperties in lowerer_class.cpp): recorded with the class
// aliases, after the packages' and the unit's classes were lowered, a
// package class's `static mb_t mb = new(K)` was known for no mailbox then
// and was built on the first reference, reading K as the module had left it.
void RegisterTypeTargets(const RtlirDesign* design, SimContext& ctx) {
  RegisterTypeDeclarations(design, ctx);
  for (const auto& [alias, target] : design->type_targets)
    ctx.RegisterTypeTarget(alias, target);
}

// §6.18 with §8.25.1: a typedef name whose chain ends in a class names that
// class -- `typedef C T;` makes `T::p` the default specialization's `C#()::p`
// -- so each such name is bound to the class it denotes, once every class of
// the design is lowered, unless the design declares a class of that name.

// §6.18 with §8.3 (printed page 180): a typedef is a class item too, and a
// class's own `typedef C#(T,CB) this_type;` names the class C throughout the
// class body and, §8.13, its subclasses' bodies, so each such typedef is
// bound under `Class::alias`, the key a nested class is held by and
// SimContext::FindClassType tries under the running method's class and its
// bases. The class the typedef names is found by its bare or scoped name as
// the design's typedefs' targets are, the parameter list a specialization
// carries naming the one declaration every specialization shares; a name
// the run holds no class for yet is left for the design-wide pass below.
// Called as the class is registered, ahead of its static initializers,
// which run its methods (Lowerer::RegisterClassDecl): bound nowhere,
// uvm_callbacks#(T,CB)'s `local static this_type m_inst` was a variable of
// no class, and `m_inst = new` stored the null handle.
// The class a typedef's declared type names, by the scoped spelling where
// it wrote one the run holds a class by, else by the bare name; null for a
// type that is no class name.
// §8.25 (printed page 204 of IEEE 1800-2023): what `typedef V#(4) t4;` writes
// is a specialization -- the generic class together with one set of actual
// parameter values -- and §8.25 makes each specialization a type of its own
// carrying its own set of static member variables, the generic class being no
// type at all. The name the typedef's own `#(...)` list spells is therefore
// what the alias is bound to, rather than the declaration's type, which
// §8.25.1 makes the default specialization alone: bound to that, `t4::W` and
// `t8::W` both read the default's W. A typedef writing no list names that
// default, which SpecializationOf answers for an empty list.
// §8.25: the type the specialization `holder` binds its own type parameter
// `pname` to, null where it binds it nothing -- the class declaration's own
// type, which §8.25.1 makes the default specialization, binds none.
static const DataType* HolderActualFor(const ClassTypeInfo* holder,
                                       std::string_view pname) {
  if (holder->param_actuals == nullptr) return nullptr;
  const ClassDecl* decl = holder->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == pname)
      return ActualForParam(*holder->param_actuals, i, pname);
  }
  return nullptr;
}

// §8.25 (printed page 204 of IEEE 1800-2023): a type parameter used in a type
// resolves to a type only after elaboration, so a class-scope typedef whose
// actuals name a type parameter of the class holding it -- UVM's `typedef
// uvm_object_registry#(T,Tname) this_type;` -- names a different
// specialization in each specialization of that class. These are the actuals
// the typedef wrote with each such name replaced by the type `holder` binds it
// to, `Box#(T)` becoming Box#(byte) under Reg#(byte); the name a named actual
// was written with is kept, the substitution being of the type alone. The list
// comes back as written where the holder binds nothing, which is the class
// declaration's own type, and for an actual naming no parameter of it.
static std::vector<DataType> TypedefActualsUnder(
    const ClassTypeInfo* holder, const std::vector<DataType>& written) {
  std::vector<DataType> bound = written;
  for (DataType& actual : bound) {
    if (actual.kind != DataTypeKind::kNamed) continue;
    if (holder->decl->type_param_names.count(actual.type_name) == 0) continue;
    const DataType* a = HolderActualFor(holder, actual.type_name);
    if (a == nullptr) continue;
    std::string_view arg = actual.param_arg_name;
    actual = *a;
    actual.param_arg_name = arg;
  }
  return bound;
}

static ClassTypeInfo* ClassNamedByTypedef(const DataType& target,
                                          const ClassTypeInfo* holder,
                                          SimContext& ctx, Arena& arena) {
  if (target.kind != DataTypeKind::kNamed) return nullptr;
  ClassTypeInfo* generic = nullptr;
  if (!target.scope_name.empty()) {
    generic = ctx.FindClassType(std::string(target.scope_name) +
                                "::" + std::string(target.type_name));
  }
  if (generic == nullptr) generic = ctx.FindClassType(target.type_name);
  if (generic == nullptr) return nullptr;
  return SpecializationOf(
      generic, TypedefActualsUnder(holder, target.type_params), ctx, arena);
}

void RegisterClassScopeTypedefAliases(ClassTypeInfo* info, SimContext& ctx,
                                      Arena& arena) {
  if (info == nullptr || info->decl == nullptr) return;
  for (const ClassMember* member : info->decl->members) {
    if (member->kind != ClassMemberKind::kTypedef ||
        member->typedef_item == nullptr) {
      continue;
    }
    auto* alias = arena.Create<std::string>(std::string(info->name) +
                                            "::" + std::string(member->name));
    if (ctx.FindClassType(*alias) != nullptr) continue;
    ClassTypeInfo* cls = ClassNamedByTypedef(member->typedef_item->typedef_type,
                                             info, ctx, arena);
    if (cls != nullptr) ctx.RegisterClassType(*alias, cls);
  }
}

void RegisterClassTypeAliases(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena) {
  for (const auto& [alias, target] : design->type_targets) {
    if (ctx.FindClassType(alias) != nullptr) continue;
    ClassTypeInfo* cls = ctx.FindClassType(target);
    if (cls != nullptr) ctx.RegisterClassType(alias, cls);
  }
  for (ClassTypeInfo* info : ctx.RegisteredClassTypes())
    RegisterClassScopeTypedefAliases(info, ctx, arena);
}

// §9.7 (printed page 245) and §8.30.1 (printed 217): the built-in class
// the declared type names, `process` or `weak_reference`, bare or through
// the std package (§26.7), by the bare name the run keys the class under.
// Empty for any other type.
static std::string UnitBuiltinClassKey(const DataType& type) {
  bool std_or_bare = type.scope_name.empty() || type.scope_name == "std";
  bool builtin =
      type.type_name == "process" || type.type_name == "weak_reference";
  if (type.kind != DataTypeKind::kNamed || !std_or_bare || !builtin) return {};
  return std::string(type.type_name);
}

// "pkg::name", the key LowerPackageClass (lowerer_import.cpp) binds a
// package's class under, where the design's package `pkg` declares a class
// so named; empty otherwise.
static std::string PackageClassKeyIn(const RtlirDesign* design,
                                     std::string_view pkg,
                                     std::string_view name) {
  for (const auto* p : design->packages) {
    if (p->name != pkg) continue;
    for (const auto* item : p->items) {
      if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
          item->class_decl->name == name)
        return std::string(pkg) + "::" + std::string(name);
    }
  }
  return {};
}

// §3.12.1 (printed page 56) with §26.3 (printed 810): the key the run holds
// the class under that a bare type name written in the compilation-unit
// scope denotes -- the unit's own class by its bare name, the name
// LowerCompilationUnitClasses binds it under and a unit declaration takes
// over an import (§26.5), else the class the first import of the unit that
// provides the name brings in, a wildcard import or an explicit import of
// that very name. Empty where neither declares a class of the name: a
// typedef, an enumeration or a type nothing declares.
static std::string UnitScopeClassKey(const RtlirDesign* design,
                                     std::string_view name) {
  for (const auto* cls : design->cu_class_decls) {
    if (cls->name == name) return std::string(name);
  }
  for (const auto* item : design->compilation_unit->cu_items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (!imp.is_wildcard && imp.item_name != name) continue;
    std::string key = PackageClassKeyIn(design, imp.package_name, name);
    if (!key.empty()) return key;
  }
  return {};
}

// The key the run holds the class under that `type`, the declared type of a
// compilation-unit variable, names: the built-in class, the package class a
// `p::C` wrote, or the class a bare name denotes in the unit's scope. Empty
// where the type names no class.
static std::string UnitClassKey(const RtlirDesign* design,
                                const DataType& type) {
  std::string key = UnitBuiltinClassKey(type);
  if (!key.empty() || type.kind != DataTypeKind::kNamed) return key;
  if (!type.scope_name.empty())
    return PackageClassKeyIn(design, type.scope_name, type.type_name);
  return UnitScopeClassKey(design, type.type_name);
}

void RegisterUnitClassVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena) {
  if (design->compilation_unit == nullptr) return;
  for (const auto* item : design->compilation_unit->cu_items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    std::string key = UnitClassKey(design, item->data_type);
    if (key.empty()) continue;
    // SimContext keys the record by string_view, and the item's name is the
    // bare key a module's `h = new` asks the class of, the storage itself
    // standing under "$unit.name" (CreateUnitDataVariables), to which
    // CarryUnitClassRecord in lowerer_package_data.cpp carries the record,
    // so the class key alone is given the design's lifetime.
    ctx.SetVariableClassType(item->name, *arena.Create<std::string>(key));
    // §8.25 (printed page 203): the specialization the declaration wrote,
    // `G #(5) b`, bound on the object its `new` constructs; nothing for a
    // bare `G b`.
    RecordClassParamActuals(item->name, key, item->data_type.type_params, ctx);
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
