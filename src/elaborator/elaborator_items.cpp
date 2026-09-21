#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/procedural_concurrent_assertion.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

uint32_t SpecparamWidth(const DataType& type, const Expr* init,
                        const TypedefMap& typedefs) {
  if (type.packed_dim_left != nullptr && type.packed_dim_right != nullptr) {
    uint32_t w = EvalTypeWidth(type);
    return w == 0 ? 32 : w;
  }
  // §6.20.5: a specify parameter with no range specification takes the range of
  // its final value, whatever expression states that value. A sized integer
  // literal carries the width directly (a 4'd5 value is 4 bits), an unsized
  // literal is 32 bits, and a signing conversion is as wide as its operand
  // under §11.7. An initializer whose width InferExprWidth cannot answer -- a
  // bare identifier, whose declaration it does not read -- keeps the 32-bit
  // default.
  if (init != nullptr) {
    uint32_t w = InferExprWidth(init, typedefs);
    return w == 0 ? 32 : w;
  }
  return 32;
}

void Elaborator::ElaborateSpecparam(ModuleItem* item, RtlirModule* mod) {
  RtlirVariable var;
  var.name = ScopedName(item->name);
  // §37.3.3: a §6.20.5 specify parameter is written in the source text like
  // any other declaration, so its object reports where.
  var.loc = item->loc;
  var.width = SpecparamWidth(item->data_type, item->init_expr, typedefs_);
  var.init_expr = item->init_expr;
  mod->variables.push_back(var);
  // §32.4.3 has an SDF LABEL section annotate to specparams, and §6.20.5 admits
  // this declaration site as much as the one inside a specify block: "A
  // specparam ... may be declared inside a specify block or in the module
  // body." RegisterModuleSpecparams (src/simulator/specify.h) binds these names
  // to SpecifyManager, and it is the lowered name -- var.name, already scoped
  // by ScopedName -- that a LABEL has to reach, because
  // SpecifyManager::ApplyAnnotatedSpecparam looks the storage up as the
  // instance prefix followed by this name.
  mod->specparam_names.push_back(var.name);
}

bool IsNameDeclared(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return true;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return true;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return true;
  }
  return false;
}

bool UnitDeclaresData(const CompilationUnit* unit, std::string_view name) {
  for (const auto* item : unit->cu_items) {
    if ((item->kind == ModuleItemKind::kVarDecl ||
         item->kind == ModuleItemKind::kNetDecl) &&
        item->name == name) {
      return true;
    }
  }
  return false;
}

// True when `name` is a parameter of `mod` that a reference standing in the
// generate blocks `scopes` can see. A parameter is a declaration of the module
// like a net or a variable, but it is held apart from both, so the implicit-net
// rule has to ask about it separately.
//
// RtlirParamDecl::name is bare whatever scope the parameter was declared in, so
// the name alone does not answer: §23.9 lists "Generate blocks" among the
// elements that "define a new scope", and a parameter one block declares is not
// visible to a reference at module level or in a sibling block. Match
// RtlirParamDecl::gen_block_prefix against the prefixes in force instead. A
// parameter of the module itself has none and is visible throughout, which is
// what §23.3.3.3 needs when such a parameter drives an input port from inside a
// generate block.
static bool IsParamDeclared(std::string_view name, const RtlirModule* mod,
                            const std::vector<std::string_view>& scopes) {
  for (const auto& p : mod->params) {
    if (p.name != name) continue;
    if (ParamVisibleFromScopes(p.gen_block_prefix, scopes)) return true;
  }
  return false;
}

bool Elaborator::MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                                        RtlirModule* mod) {
  // Ask IsNameDeclared about one key per enclosing scope, innermost first.
  // §6.10 assumes an implicit net for an identifier that "has not been declared
  // previously in the scope where the continuous assignment statement appears
  // or in any scope whose declarations can be directly referenced from" that
  // scope, and §23.9 lists the scopes and fixes the order: an identifier
  // "referenced directly (without a hierarchical path) within a ... generate
  // block ... shall be declared either within the ... generate block locally or
  // within a module, interface, program, checker, task, function, named block,
  // or generate block that is higher in the same branch of the name tree", and
  // "the search shall continue upward until an item by that name is found or
  // until a module, interface, program, or checker boundary is encountered".
  //
  // RtlirModule::nets, RtlirModule::variables and RtlirModule::ports hold the
  // string Elaborator::ScopedName produced, so the key for each scope is that
  // scope's generate prefix followed by the identifier. gen_prefix_scopes_
  // holds those prefixes outermost first, and the module itself is the bare
  // identifier. Outside a generate block gen_prefix_scopes_ is empty and the
  // bare key is the only one.
  //
  // Dropping any of them is a defect. Without the innermost key a second
  // reference to one undeclared identifier in one generate block pushes a
  // second net of that name, which SimContext::CreateNet in
  // src/simulator/sim_context.cpp then registers over the first. Without the
  // bare key a reference in a generate block to a net the module declares gains
  // a prefixed net that shadows it, and the continuous assignment drives the
  // new net. Without the keys in between the same shadowing happens one block
  // in: inside block 'a' nested in block 'b', a net that 'b' declares is held
  // as "b_w", which neither "b_a_w" nor "w" matches.
  for (auto it = gen_prefix_scopes_.rbegin(); it != gen_prefix_scopes_.rend();
       ++it) {
    if (IsNameDeclared(std::string(*it) + std::string(name), mod)) return true;
  }
  if (IsNameDeclared(name, mod)) return true;
  // §6.10 gives an implicit net to an identifier used in a port connection or
  // on the left of a continuous assignment only when it is not declared. A
  // parameter is declared, and §23.3.3.3 lets any expression drive an input
  // port, so a parameter named as a port actual is the expression that drives
  // it. Creating a scalar net of the same name here would instead shadow the
  // parameter with an undriven wire and deliver zero to the port.
  if (IsParamDeclared(name, mod, gen_prefix_scopes_)) return true;
  // §3.12.1 (printed page 56) searches the compilation-unit scope for a name
  // the module does not declare, so its declarations are among those §6.10
  // (printed 108) lets the reference reach, and §10.3.2 (printed 249) lets a
  // continuous assignment drive a variable. `int g;` outside every module with
  // `assign g = 1;` in a module got an implicit net `g` shadowing the unit's.
  if (UnitDeclaresData(unit_, name)) return true;
  if (unit_->default_nettype == NetType::kNone) {
    diag_.Error(loc,
                std::format("implicit net '{}' forbidden by "
                            "`default_nettype none",
                            name),
                Subclause("22.8"));
    return false;
  }
  // §6.10: an identifier used in an instance terminal/port-connection list or
  // on the left side of a continuous assignment gets an implicit scalar net of
  // the default net type. It shares the implicit-net constructor with the
  // port-expression case; here the width is scalar and the net is unsigned.
  //
  // The redeclaration key carries the generate prefix and net_names_ does not,
  // which is what Elaborator::ElaborateNetDecl does for an explicit net at
  // src/elaborator/elaborator_decls.cpp:598 and :600. §6.10 settles the first:
  // "if the implicit net is declared by a reference in a generate block, then
  // the net is implicitly declared only in that generate block". The name this
  // reference declares therefore belongs to the block, and a declaration of it
  // in another block or in the module is a different scope rather than a
  // redeclaration of this one.
  //
  // net_names_ answers a different question -- whether a simple name written
  // in this module names a net rather than a variable -- and every one of its
  // readers looks it up by the identifier the source wrote.
  // Elaborator::ValidateContAssignIdentLhs in
  // src/elaborator/elaborator_cont_assign.cpp is the closest: it passes `name`
  // here and then reads net_names_ back with that same `name`, so a prefixed
  // entry would make it treat the net it just created as a variable and report
  // a second assignment to it under §10.3.2.
  std::string_view scoped = ScopedName(name);
  RtlirNet net =
      MakeImplicitPortNet(scoped, /*port_width=*/1, /*port_is_signed=*/false,
                          unit_->default_nettype);
  // §23.4: a nested module sees the enclosing modules' names, so the reference
  // may name an outer object rather than declare a net of its own; the net is
  // pushed either way, for the assignment to lower against, and
  // RtlirNet::refers_outward tells Lowerer which. §6.10 gives a name declared
  // nowhere to the scope of the reference, so it is the nested module's own.
  net.refers_outward = IsNameInEnclosingScope(name);
  mod->nets.push_back(net);
  declared_names_.insert(scoped);
  net_names_.insert(name);
  return true;
}

void Elaborator::ValidateTypenameAsElabConstant(const Expr* init) {
  if (init->kind != ExprKind::kSystemCall) return;
  if (init->callee != "$typename") return;
  if (init->args.empty()) return;
  const auto* arg = init->args[0];
  if (arg->kind == ExprKind::kMemberAccess) {
    diag_.Error(arg->range.start,
                "$typename argument in elaboration-time-constant context "
                "shall not contain hierarchical references",
                Subclause("20.6.1"));
    return;
  }
  if (arg->kind != ExprKind::kSelect) return;
  auto it = var_array_info_.find(arg->base->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_dynamic && !it->second.is_assoc) return;
  diag_.Error(arg->range.start,
              "$typename argument in elaboration-time-constant context "
              "shall not reference elements of dynamic objects",
              Subclause("20.6.1"));
}

namespace {

// §28.3.6: validates the per-terminal bit-lengths of a gate, switch or
// user-defined primitive instance array whose instance range has already been
// confirmed present. `scope` is the caller's parameter scope used to evaluate
// the range bounds. An interconnect terminal must match the instance-array
// length exactly; an ordinary terminal must be either scalar-width (broadcast)
// or equal to the array length. §29.8 puts an array of primitive instances
// under the same rule -- "The terminal connection rules remain the same as
// outlined in 28.3.6" -- so the reports name a primitive as well as a gate,
// and cite 28.3.6, which is where the rule is stated.
void CheckGateInstanceArrayTerminalWidths(
    const ModuleItem* item, const RtlirModule* mod, const ScopeMap& scope,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  auto len = InstanceArrayLength(item, scope);
  if (!len) {
    diag.Error(item->loc,
               "gate, switch or primitive instance range bound is not a "
               "constant expression",
               Subclause("28.3.5"));
    return;
  }
  uint32_t array_len = *len;
  for (auto* term : item->gate_terminals) {
    uint32_t w = LookupLhsWidth(term, mod);
    if (w == 0) continue;
    bool is_interconnect = term && term->kind == ExprKind::kIdentifier &&
                           interconnect_names.count(term->text) != 0;
    if (is_interconnect) {
      if (w != array_len) {
        diag.Error(item->loc,
                   "interconnect terminal of a gate or primitive instance "
                   "array must have a bit-length equal to the instance-array "
                   "length",
                   Subclause("28.3.6"));
        break;
      }
      continue;
    }
    if (w != 1 && w != array_len) {
      diag.Error(item->loc,
                 "gate or primitive array terminal width does not match "
                 "either the per-instance port width or the instance-array "
                 "length",
                 Subclause("28.3.6"));
      break;
    }
  }
}

// Emits the redeclaration and dynamic-override-specifier diagnostics for a
// function or task declaration item. Records `scoped_name` in
// `declared_names`, which is the name keyed by the scope the declaration
// stands in, and reports the name the source wrote.
void CheckFunctionDeclDiagnostics(
    const ModuleItem* item, std::string_view scoped_name,
    std::unordered_set<std::string_view>& declared_names, DiagEngine& diag) {
  if (!item->name.empty() && !declared_names.insert(scoped_name).second) {
    diag.Error(item->loc, std::format("redeclaration of '{}'", item->name),
               Subclause("23.9"));
  }
  if (item->method_class.empty() &&
      (item->is_method_initial || item->is_method_extends ||
       item->is_method_final)) {
    diag.Error(item->loc,
               "dynamic_override_specifiers shall only be legal on "
               "method declarations inside a non-interface class scope",
               Subclause("8.20"));
  }
}

// Emits the gate-instance name-conflict and redeclaration diagnostics. Records
// `scoped_inst_name` in `declared_names`, which is the instance name keyed by
// the scope the gate instance stands in, and reports the name the source
// wrote. The conflict with the output net is a comparison between two names
// the source wrote, so it reads item->gate_inst_name on both sides.
void CheckGateInstNameDiagnostics(
    const ModuleItem* item, std::string_view scoped_inst_name,
    std::unordered_set<std::string_view>& declared_names, DiagEngine& diag) {
  if (!item->gate_inst_name.empty() && !item->gate_terminals.empty() &&
      item->gate_terminals[0] &&
      item->gate_terminals[0]->kind == ExprKind::kIdentifier &&
      item->gate_terminals[0]->text == item->gate_inst_name) {
    diag.Error(item->loc,
               std::format("gate instance name '{}' conflicts with its "
                           "output net",
                           item->gate_inst_name),
               Subclause("23.9"));
  }
  if (!item->gate_inst_name.empty() &&
      !declared_names.insert(scoped_inst_name).second) {
    diag.Error(item->loc,
               std::format("redeclaration of '{}'", item->gate_inst_name),
               Subclause("23.9"));
  }
}

// Emits the UDP-instance redeclaration diagnostic and records
// `scoped_inst_name`, the instance name keyed by the scope the UDP instance
// stands in. The report names the instance as the source wrote it.
void CheckUdpInstNameDiagnostics(
    const ModuleItem* item, std::string_view scoped_inst_name,
    std::unordered_set<std::string_view>& declared_names, DiagEngine& diag) {
  if (!item->gate_inst_name.empty() &&
      !declared_names.insert(scoped_inst_name).second) {
    diag.Error(item->loc,
               std::format("redeclaration of '{}'", item->gate_inst_name),
               Subclause("23.9"));
  }
}

// Builds an RTLIR import record from an import-declaration item and appends it
// to the module's import list.
void RecordImportDecl(const ModuleItem* item, RtlirModule* mod) {
  RtlirImport imp;
  imp.package_name = item->import_item.package_name;
  imp.item_name = item->import_item.item_name;
  imp.is_wildcard = item->import_item.is_wildcard;
  mod->imports.push_back(imp);
}

// Records a class declaration's name (and parameterized status) and pushes the
// class decl onto the module per §8.
void RecordClassDecl(
    const ModuleItem* item, RtlirModule* mod,
    std::unordered_set<std::string_view>& class_names,
    std::unordered_set<std::string_view>& parameterized_class_names) {
  if (!item->class_decl) return;
  class_names.insert(item->class_decl->name);
  if (!item->class_decl->params.empty()) {
    parameterized_class_names.insert(item->class_decl->name);
  }
  mod->class_decls.push_back(item->class_decl);
}

// §6.10: every undeclared identifier in a primitive/alias terminal list becomes
// an implicit scalar net; `make_net` creates one net per identifier terminal.
template <typename MakeNet>
void CreateImplicitNetsForTerminals(const std::vector<Expr*>& terminals,
                                    SourceLoc loc, MakeNet&& make_net) {
  for (auto* term : terminals) {
    if (term && term->kind == ExprKind::kIdentifier) {
      make_net(term->text, loc);
    }
  }
}

bool HasInstanceArrayRange(const ModuleItem* item) {  // §28.3.6
  return item->inst_range_left != nullptr && item->inst_range_right != nullptr;
}

}  // namespace

// The instance range is what makes §28.3.6's widths a question at all, so an
// item carrying none is left alone by CheckGateInstanceArrayTerminalWidths: its
// rule is about "the bit length of each single-instance port or terminal in the
// instantiated module or primitive" against the length of an array, and there
// is no array here to measure against.
// ValidatePrimitiveOutputTerminalWidths asks the complementary question, so it
// is asked of every item, and one ScopeMap answers both.
void Elaborator::CheckInstanceTerminalWidths(const ModuleItem* item,
                                             const RtlirModule* mod) {
  ScopeMap scope = BuildParamScope(mod);
  if (HasInstanceArrayRange(item)) {
    CheckGateInstanceArrayTerminalWidths(item, mod, scope, interconnect_names_,
                                         diag_);
  }
  ValidatePrimitiveOutputTerminalWidths(item, mod, scope, diag_);
}

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  // §28.16: every delay a source can write reaches this walk, and each is
  // checked before the item is built. The nine slots live on the item rather
  // than on what it becomes, so one place sees the net delays, the continuous
  // assignment's and the gate or primitive instance's alike.
  if (ItemCarriesDelay(item)) {
    ValidateItemDelaysNonNegative(item, BuildParamScope(mod), diag_);
  }
  if (ElaborateDeclItem(item, mod)) return;
  ElaborateBehavioralItem(item, mod);
}

// §8.26: a class declared inside a module. Its name and parameterized status go
// onto the module, and §6.20.1 makes every param_assignment in its body a
// localparam whose value is a constant expression -- said of a class declared
// here as much as of one declared at compilation-unit scope, where
// RegisterClassParams asks it. The module's own parameter scope is what such a
// default folds against, since §6.20.1's constant expression is constant in the
// scope the class stands in.
void Elaborator::ElaborateModuleClassDecl(ModuleItem* item, RtlirModule* mod) {
  RecordClassDecl(item, mod, class_names_, parameterized_class_names_);
  if (item->class_decl == nullptr) return;
  RegisterModuleClassParams(item->class_decl, BuildParamScope(mod),
                            cu_param_scope_, arena_, diag_);
  // §8.23: the class's typedefs are reached through its name from outside
  // the class, `Node::value_t v;` in the module's own procedure, and the
  // "Class::name" key is what the type tables answer such a name by;
  // RegisterClassTypedefs in elaborator_resolve.cpp keys the compilation
  // unit's classes so, and a class of a module had no key at all, so a local
  // declared with the name was sized as a name nothing could resolve.
  for (const auto* m : item->class_decl->members) {
    if (m->kind != ClassMemberKind::kTypedef || m->typedef_item == nullptr)
      continue;
    auto* key = arena_.Create<std::string>(std::string(item->class_decl->name) +
                                           "::" + std::string(m->name));
    typedefs_[*key] = m->typedef_item->typedef_type;
  }
  // §13.3 with §7.2.1: the class's methods are reached by no item walk, so
  // their inline aggregate formals are resolved here, against the module's
  // typedefs as they stand at the declaration and the class's own (§8.23),
  // as ElaborateBehavioralItem resolves the module's own subroutines. A
  // member naming a typedef the module forward-declares above the class and
  // defines below it (§6.18) finds a placeholder here and is resolved by
  // ResolveModuleClassFormalTypes once the walk has reached the definition.
  ResolveClassMethodFormalTypes(item->class_decl, typedefs_, arena_);
}

// Declarations, types, instances, and structural items (§6, §23, §25, §28).
bool Elaborator::ElaborateDeclItem(ModuleItem* item, RtlirModule* mod) {
  auto make_implicit_net = [&](std::string_view n, SourceLoc l) {  // §6.10
    MaybeCreateImplicitNet(n, l, mod);
  };
  switch (item->kind) {
    case ModuleItemKind::kNetDecl:
      ElaborateNetDecl(item, mod);
      return true;
    case ModuleItemKind::kVarDecl:
      ElaborateVarDecl(item, mod);
      return true;
    case ModuleItemKind::kContAssign:
      ElaborateContAssign(item, mod);
      return true;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      return true;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      return true;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      return true;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      return true;
    case ModuleItemKind::kGateInst:
      // §27.4: a generate block "comprises a separate scope and a new level of
      // hierarchy when it is instantiated", so a gate instance written in a
      // loop generate body declares its name afresh in each iteration rather
      // than again, and is keyed by the generate prefix that tells those
      // scopes apart. Outside a generate block ScopedName hands the name back
      // unchanged, so a repeat at module level is still a redeclaration. The
      // empty check guards it: ScopedName("") returns the prefix itself, which
      // would key an unnamed gate instance under the block's own name.
      CheckGateInstNameDiagnostics(item,
                                   item->gate_inst_name.empty()
                                       ? item->gate_inst_name
                                       : ScopedName(item->gate_inst_name),
                                   declared_names_, diag_);
      CreateImplicitNetsForTerminals(item->gate_terminals, item->loc,
                                     make_implicit_net);
      CheckInstanceTerminalWidths(item, mod);
      ValidateBidirectionalSwitchConnections(item, mod, diag_,
                                             nettype_canonical_);
      ElaborateGateInst(item, mod, arena_, BuildParamScope(mod));
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      return true;
    case ModuleItemKind::kUdpInst:
      // §27.4 keys the instance name by the generate block instance it stands
      // in, as the kGateInst case above does and for the same reason.
      CheckUdpInstNameDiagnostics(item,
                                  item->gate_inst_name.empty()
                                      ? item->gate_inst_name
                                      : ScopedName(item->gate_inst_name),
                                  declared_names_, diag_);
      CreateImplicitNetsForTerminals(item->gate_terminals, item->loc,
                                     make_implicit_net);
      // Checked before ElaborateUdpInst expands the array, so a terminal the
      // widths rule rejects is reported rather than expanded.
      CheckInstanceTerminalWidths(item, mod);
      ElaborateUdpInst(item, mod);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      return true;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      const_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      return true;
    case ModuleItemKind::kAlias: {
      CreateImplicitNetsForTerminals(item->alias_nets, item->loc,
                                     make_implicit_net);
      ValidateAlias(item, mod);
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      return true;
    }
    case ModuleItemKind::kImportDecl:
      // §26.3: the package's typedefs and parameters become visible from here
      // on, so they are registered as this item is reached rather than ahead of
      // the walk. RecordImportDecl only mirrors the directive into the RTLIR.
      ApplyBodyImport(item->import_item);
      RecordImportDecl(item, mod);
      return true;
    case ModuleItemKind::kClassDecl:
      ElaborateModuleClassDecl(item, mod);
      return true;
    default:
      return false;
  }
}

// Processes, generates, subroutines, assertions, and remaining items (§9, §16,
// §13, §27).
//
// §14.14: a procedure names $global_clock either in its own sensitivity list
// (`always @($global_clock)`) or in an event control within its body
// (`initial @($global_clock) done = 1;`). Both are rewritten into the effective
// global clocking declaration's event expression, which is handed to
// AddProcess in ProcessBuildEnv::global_clocking_event and written onto the
// process rather than onto `item`. `item` belongs to the one ModuleDecl the
// parser built for the module, and two instances of that module can inherit
// different events under rule b), so a rewrite made on `item` would give both
// whichever instance was elaborated first.
bool Elaborator::ElaborateBehavioralItem(ModuleItem* item, RtlirModule* mod) {
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_, &const_names_,
                             module_global_clocking_event_};
  // An initial or final procedure never infers a sensitivity list, so the two
  // members BuildProcessWithSensitivity consults only when inferring one --
  // func_map and const_names -- are left at their defaults.
  const ProcessBuildEnv kNoInferenceEnv{
      .arena = arena_,
      .diag = diag_,
      .global_clocking_event = module_global_clocking_event_};
  switch (item->kind) {
    case ModuleItemKind::kInitialBlock:
      ElaborateProceduralConcurrentAssertions(item, mod, property_registry_,
                                              arena_, diag_);
      AddProcess(RtlirProcessKind::kInitial, item, mod, kNoInferenceEnv);
      return true;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod, kNoInferenceEnv);
      return true;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      // §16.14.6: the concurrent assertions the procedure embeds take their
      // clock from it, or from the default clocking, before the process is
      // built over its body.
      ElaborateProceduralConcurrentAssertions(item, mod, property_registry_,
                                              arena_, diag_);
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, kEnv);
      return true;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      // §26.3: an imported name is locally visible only "prior to that point
      // within the current scope", so copy typedefs_ and cu_param_scope_ onto
      // the pending entry here, where they hold the scope this generate was
      // written in. Elaborator::ResolveDefparamsAndGenerates folds the
      // condition after every module has been elaborated, and without the copy
      // it would fold against the union of every module's imports.
      //
      // func_decls_ is copied for the same reason and reaches §13.4.3 rather
      // than §26.3: Elaborator::ElaborateItems filled it from this module's
      // ModuleDecl before the item loop that reached here, and
      // ItemElaborationStateSaver takes it back out when the module returns,
      // and property_registry_ for §16.12's instances of a named property or
      // sequence, which it fills and takes back the same way.
      pending_generates_.push_back({item, mod, typedefs_, cu_param_scope_,
                                    func_decls_, property_registry_});
      return true;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      // §27.4 keys the name by the generate block instance the declaration
      // stands in, as the kGateInst case in Elaborator::ElaborateDeclItem does
      // and for the same reason.
      CheckFunctionDeclDiagnostics(
          item, item->name.empty() ? item->name : ScopedName(item->name),
          declared_names_, diag_);
      ValidateFunctionBody(item);
      ValidateFunctionArgDefaultsScope(item);
      ResolveFormalAggregateTypes(item, typedefs_, arena_);
      ElaborateSubroutineConcurrentAssertions(item, mod, property_registry_,
                                              arena_, diag_);
      mod->function_decls.push_back(item);
      return true;
    case ModuleItemKind::kElabSystemTask:
      ValidateElabSystemTask(item, mod);
      return true;
    case ModuleItemKind::kDpiImport:
      ValidateDpiImport(item);
      mod->dpi_import_decls.push_back(item);
      return true;
    case ModuleItemKind::kLetDecl:
      ValidateLetDecl(item);
      let_names_.insert(item->name);
      mod->let_decls.push_back(item);
      return true;
    case ModuleItemKind::kSpecifyBlock:
      RegisterSpecifyBlockSpecparams(item, mod, typedefs_, specparam_names_,
                                     const_names_);
      mod->specify_blocks.push_back(item);
      return true;
    case ModuleItemKind::kCovergroupDecl:
      // §19.3 (footnote 29): the extends form of a covergroup is legal only
      // within a class. The grammar accepts `covergroup extends base ;` in any
      // scope, so the restriction is a semantic one applied here. A covergroup
      // declaration handled as a module item belongs to a module, interface,
      // checker, or program — class covergroups are elaborated as class
      // members and never reach this path — so an inherited base is illegal.
      if (!item->covergroup_extends_base.empty()) {
        diag_.Error(item->loc,
                    "a covergroup may only use 'extends' inside a class",
                    Subclause("19.3"));
      }
      mod->let_decls.push_back(item);
      return true;
    case ModuleItemKind::kDpiExport:
      // §35.7: an export declaration has no effect on SystemVerilog usage of
      // the subroutine it names, so it is held apart from let_decls, whose
      // entries the run resolves a call to before it reaches a function.
      mod->dpi_export_decls.push_back(item);
      return true;
    default:
      return ElaborateAssertionItem(item, mod);
  }
}

}  // namespace delta
