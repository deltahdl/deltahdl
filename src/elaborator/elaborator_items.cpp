#include <cmath>
#include <cstdlib>
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
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ElaborateSpecparam(ModuleItem* item, RtlirModule* mod) {
  RtlirVariable var;
  var.name = ScopedName(item->name);
  if (item->data_type.packed_dim_left && item->data_type.packed_dim_right) {
    var.width = EvalTypeWidth(item->data_type);
    if (var.width == 0) var.width = 32;
  } else if (item->init_expr &&
             item->init_expr->kind == ExprKind::kIntegerLiteral) {
    // §6.20.5: a specify parameter with no range specification takes the range
    // of its final value. A sized integer literal carries that width directly
    // (a 4'd5 value is 4 bits); an unsized literal is 32 bits. Non-literal or
    // non-integer initializers keep the 32-bit default.
    uint32_t w = InferExprWidth(item->init_expr, typedefs_);
    var.width = w == 0 ? 32 : w;
  } else {
    var.width = 32;
  }
  var.init_expr = item->init_expr;
  mod->variables.push_back(var);
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

// §6.20.3: a data type parameter (parameter type) can only be set to a data
// type. The parser marks a type parameter with a void data type; if such a
// parameter received an ordinary value expression instead of a type, it has
// been set to a non-type and must be rejected.
void CheckTypeParamNotSetToValue(const ModuleItem* item, DiagEngine& diag) {
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit &&
      item->init_expr != nullptr &&
      item->init_expr->kind != ExprKind::kTypeRef) {
    diag.Error(item->loc,
               std::format("type parameter '{}' can only be set to a data "
                           "type, not a value expression",
                           item->name),
               Subclause("6.20.3"));
  }
}

// §6.20.3: a type parameter declared with a leading basic-data-type keyword
// (enum, struct, union, class, or interface class) restricts its valid types;
// assigning a type that does not conform to that keyword is an error. The
// assigned type is resolved through any typedef chain first, and only a
// definite mismatch is flagged -- a still-named type is left alone, since it
// may resolve to a conforming type declared elsewhere.
//
// On a type-parameter item the restriction keyword is carried in
// forward_type_kind as: kEnum/kStruct/kUnion for those aggregate keywords,
// kNamed for a `class` restriction, and kVoid for `interface class` (see
// Parser::ParseTypeParamDecl).
// Follow a chain of typedef names to the concrete type behind it, stopping at
// a name with no definition. The hop limit keeps a cyclic typedef from looping.
const DataType* ResolveNamedTypeChain(const DataType* dtype,
                                      const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8 && dtype->kind == DataTypeKind::kNamed; ++hops) {
    auto td = typedefs.find(dtype->type_name);
    if (td == typedefs.end()) break;
    dtype = &td->second;
  }
  return dtype;
}

// §6.20.3: "it shall be an error if the type parameter is assigned a type
// definition that does not conform to the specified basic data type" (printed
// page 128 of ~/LRM.pdf). `class` and `interface class` are two of the five
// basic data types that clause lists, and §8.26 makes them different kinds of
// declaration, so a type conforming to one does not conform to the other.
//
// Four answers, and the declaration decides them. A class (or interface class)
// type is always referenced by name, so a resolved concrete type -- a built-in
// scalar or vector, an enum, a struct or a union -- is not a class at all. A
// name that reaches a ClassDecl conforms when that declaration's kind is the
// restricted one. A name known to be a class that reaches no ClassDecl is taken
// as an ordinary class. A name that is neither conforms to neither restriction,
// because nothing makes it a class.
//
// Deciding from DataTypeKind alone is what let the second and fourth of those
// through: every name survives typedef resolution as kNamed, so an ordinary
// class assigned to an `interface class` restriction and a name nothing
// declares were both accepted in silence, and `fwd` reached the function only
// to pick a word for the message.
struct ClassTypeLookup {
  // Carries each ClassDecl, and so is what says whether a class is an interface
  // class.
  const CompilationUnit* unit;
  // The names known to be classes. It holds two kinds FindClassDecl cannot
  // return a declaration for: the built-in classes, which have no declaration
  // to find, and a name declared as a class in more than one scope, which
  // FindClassDecl reports as ambiguous by returning null. Neither is an
  // interface class as far as anything here can tell, and both are classes, so
  // the set decides only whether the name is one -- never which kind.
  const std::unordered_set<std::string_view>* names;
};

void CheckTypeParamIsClass(const ModuleItem* item, DataTypeKind fwd,
                           const DataType& resolved,
                           const ClassTypeLookup& lookup, DiagEngine& diag) {
  const bool kWantsInterface = fwd == DataTypeKind::kVoid;
  // The article travels with the noun. Written as a literal `a` before a
  // substituted noun it read "restricted to a interface class type".
  const std::string_view kRestriction =
      kWantsInterface ? "an interface class" : "a class";
  if (resolved.kind != DataTypeKind::kNamed) {
    diag.Error(item->loc,
               std::format("type parameter '{}' is restricted to {} type but "
                           "is assigned a type that is not a class",
                           item->name, kRestriction),
               Subclause("6.20.3"));
    return;
  }
  const ClassDecl* cls = FindClassDecl(resolved.type_name, lookup.unit);
  const bool kIsKnownClass = cls || lookup.names->count(resolved.type_name) > 0;
  if (!kIsKnownClass) {
    diag.Error(item->loc,
               std::format("type parameter '{}' is restricted to {} type but "
                           "is assigned '{}', which no class declaration "
                           "defines",
                           item->name, kRestriction, resolved.type_name),
               Subclause("6.20.3"));
    return;
  }
  const bool kIsInterface = cls && cls->is_interface;
  if (kIsInterface == kWantsInterface) return;
  diag.Error(
      item->loc,
      std::format("type parameter '{}' is restricted to {} type but is "
                  "assigned '{}', which is {}",
                  item->name, kRestriction, resolved.type_name,
                  kIsInterface ? "an interface class" : "an ordinary class"),
      Subclause("6.20.3"));
}

// §6.20.3: a type parameter restricted to enum, struct, or union conforms
// only if the type it is assigned resolves to that same kind.
void CheckTypeParamIsAggregateKind(const ModuleItem* item, DataTypeKind fwd,
                                   const DataType& resolved, DiagEngine& diag) {
  if (resolved.kind == DataTypeKind::kNamed || resolved.kind == fwd) return;
  static const auto kBasicName = [](DataTypeKind k) -> std::string_view {
    switch (k) {
      case DataTypeKind::kEnum:
        return "enum";
      case DataTypeKind::kStruct:
        return "struct";
      case DataTypeKind::kUnion:
        return "union";
      default:
        return "type";
    }
  };
  diag.Error(item->loc,
             std::format("type parameter '{}' is assigned a type that does "
                         "not conform to the required {} kind",
                         item->name, kBasicName(fwd)),
             Subclause("6.20.3"));
}

void CheckTypeParamConformsToForwardKind(const ModuleItem* item, bool is_type,
                                         const TypedefMap& typedefs,
                                         const ClassTypeLookup& lookup,
                                         DiagEngine& diag) {
  if (!is_type) return;
  DataTypeKind fwd = item->forward_type_kind;
  bool aggregate_restriction = fwd == DataTypeKind::kEnum ||
                               fwd == DataTypeKind::kStruct ||
                               fwd == DataTypeKind::kUnion;
  bool class_restriction =
      fwd == DataTypeKind::kNamed || fwd == DataTypeKind::kVoid;
  if (!aggregate_restriction && !class_restriction) return;

  const DataType* resolved =
      ResolveNamedTypeChain(&item->typedef_type, typedefs);
  if (class_restriction) {
    CheckTypeParamIsClass(item, fwd, *resolved, lookup, diag);
    return;
  }
  CheckTypeParamIsAggregateKind(item, fwd, *resolved, diag);
}

// Fills the value-parameter type information on `pd` and records a real-typed
// parameter in `real_param_names`, which is the set CheckRealSelectNode in
// src/elaborator/elaborator_validate.cpp reads to reject a later bit-select or
// part-select of it. §11.5.1 states one sentence -- "A bit-select or
// part-select of a scalar, or of a real variable or real parameter, shall be
// illegal" -- whose second alternative names a real parameter, so the name goes
// in the set standing for that alternative rather than in scalar_var_names_,
// which stands for the first.
//
// A parameter carrying an unpacked dimension stays out, because §11.5.2 makes
// an address written after such a name an array element select: `parameter real
// P[4] = '{default: 0.0}; v = P[0];` reads one real element and is legal.
void PopulateValueParamInfo(
    RtlirParamDecl& pd, const ModuleItem* item,
    std::unordered_set<std::string_view>& real_param_names) {
  PopulateParamTypeInfo(pd, item->data_type);
  if (item->unpacked_dims.empty() && IsRealType(item->data_type.kind)) {
    real_param_names.insert(item->name);
  }
}

// Const-evaluates a parameter's initializer against `scope` and records the
// resolved value on `pd`. §6.20.2: a parameter declared real takes a real
// value, and an integer-typed parameter initialized from a real constant rounds
// to the nearest integer (ties away from zero). A parameter declared `string`
// also keeps its characters, which `arena` owns (§6.16).
void ResolveParamConstValue(RtlirParamDecl& pd, const ModuleItem* item,
                            bool is_type, const ScopeMap& scope, Arena& arena) {
  // The real fold comes first, because an integer fold of a real-typed
  // parameter's initializer succeeds whenever the value happens to have no
  // fraction and would then store it as the integer it is not.
  if (!is_type &&
      TryFoldRealParamValue(pd, item->init_expr, item->data_type, scope))
    return;
  auto val = ConstEvalInt(item->init_expr, scope);
  if (val) {
    pd.resolved_value = *val;
    pd.is_resolved = true;
  } else if (!is_type && ParamExpectsIntegerValue(pd, item->data_type)) {
    if (auto rval = ConstEvalReal(item->init_expr, scope)) {
      pd.resolved_value = std::llround(*rval);
      pd.is_resolved = true;
    }
  }
  if (!is_type)
    RecordStringParamValue(pd, item->init_expr, &item->data_type, arena);
}

}  // namespace

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  bool is_type = item->data_type.kind == DataTypeKind::kVoid &&
                 item->typedef_type.kind != DataTypeKind::kImplicit;

  // §6.23/§6.20.3: a type-parameter default written with the type operator,
  // e.g. `localparam type T = type(int)`, arrives as a kTypeRef init expression
  // (its text is the inner type name) rather than a typedef_type. Resolve it to
  // a concrete type so dependent declarations elaborate against the chosen
  // type, carrying the built-in's implicit signedness (so `T x` is signed for
  // int). §8.23 also permits a class scope resolution to prefix that type name,
  // as in `type(Frame::payload_t)`, which the kTypeRef expression carries in
  // scope_prefix. Resolve that form through the class instead, and leave
  // typedef_type unchanged when the class or its typedef is not visible.
  if (!is_type && item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit && item->init_expr &&
      item->init_expr->kind == ExprKind::kTypeRef &&
      !item->init_expr->text.empty()) {
    if (item->init_expr->scope_prefix.empty()) {
      item->typedef_type = TypeNameToDataType(item->init_expr->text);
    } else if (const DataType* scoped =
                   FindClassScopedTypedefType(item->init_expr->scope_prefix,
                                              item->init_expr->text, unit_)) {
      item->typedef_type = *scoped;
    }
    is_type = item->typedef_type.kind != DataTypeKind::kImplicit;
  }

  CheckTypeParamNotSetToValue(item, diag_);
  CheckTypeParamConformsToForwardKind(
      item, is_type, typedefs_, ClassTypeLookup{unit_, &class_names_}, diag_);

  if (is_type) {
    typedefs_[item->name] = item->typedef_type;
  }
  RtlirParamDecl pd;
  pd.name = item->name;
  // §27.4: a generate block "comprises a separate scope and a new level of
  // hierarchy when it is instantiated", and this site elaborates a parameter
  // written in one as readily as one written among a module's own items.
  pd.gen_block_prefix = InternedGenPrefix();
  pd.is_type_param = is_type;

  pd.is_localparam = item->is_localparam || mod->has_param_port_list;
  pd.default_value = item->init_expr;
  if (!is_type) {
    PopulateValueParamInfo(pd, item, real_param_names_);
    // §11.5.1: a select on this parameter names bits by their index in the
    // range it is declared with, so keep the two bounds. They are folded
    // against the parameters already elaborated, which is what a bound written
    // in terms of an earlier parameter needs.
    RecordParamDeclRange(pd, item->data_type, BuildParamScope(mod));
  }

  // §6.20.7: a parameter is unbounded if it is assigned a literal '$', or if it
  // is assigned another (unbounded) parameter; the assigned-to parameter is
  // itself unbounded in that case.
  if (item->init_expr && item->init_expr->kind == ExprKind::kIdentifier &&
      (item->init_expr->text == "$" ||
       RefersToUnboundedParam(mod, item->init_expr->text))) {
    pd.is_unbounded = true;
  } else if (item->init_expr) {
    if (ContainsDollarSubexpr(item->init_expr)) {
      // §6.20.7: $ must be the entire, self-contained parameter value; it may
      // not be combined with operators or selects in this context.
      diag_.Error(item->loc,
                  std::format("'$' may only be assigned to parameter '{}' as a "
                              "complete, self-contained expression",
                              item->name),
                  Subclause("6.20.7"));
    }
    ValidateTypenameAsElabConstant(item->init_expr);
    auto scope = BuildParamScope(mod);
    ResolveParamConstValue(pd, item, is_type, scope, arena_);
  }
  mod->params.push_back(pd);

  const_names_.insert(item->name);
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
  auto lhi = ConstEvalInt(item->inst_range_left, scope);
  auto rhi = ConstEvalInt(item->inst_range_right, scope);
  if (!lhi || !rhi) {
    diag.Error(item->loc,
               "gate, switch or primitive instance range bound is not a "
               "constant expression",
               Subclause("28.3.5"));
    return;
  }
  auto array_len = static_cast<uint32_t>(std::abs(*lhi - *rhi) + 1);
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
  if (ElaborateDeclItem(item, mod)) return;
  ElaborateBehavioralItem(item, mod);
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
      ElaborateGateInst(item, mod, arena_);
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
      RecordClassDecl(item, mod, class_names_, parameterized_class_names_);
      return true;
    default:
      return false;
  }
}

// Processes, generates, subroutines, assertions, and remaining items (§9, §16,
// §13, §27).
bool Elaborator::ElaborateBehavioralItem(ModuleItem* item, RtlirModule* mod) {
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_, &const_names_};
  switch (item->kind) {
    case ModuleItemKind::kInitialBlock:
      AddProcess(RtlirProcessKind::kInitial, item, mod,
                 ProcessBuildEnv{arena_, diag_});
      return true;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod,
                 ProcessBuildEnv{arena_, diag_});
      return true;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
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
      // ItemElaborationStateSaver takes it back out when the module returns.
      pending_generates_.push_back(
          {item, mod, typedefs_, cu_param_scope_, func_decls_});
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
      RegisterSpecifyBlockSpecparams(item, mod, specparam_names_, const_names_);
      mod->let_decls.push_back(item);
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
