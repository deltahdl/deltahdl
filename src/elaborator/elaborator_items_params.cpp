// A value or type parameter declaration written among a module's items
// (§6.20.2, §6.20.3), moved out of src/elaborator/elaborator_items.cpp, which
// holds the item walk, at its size limit.

#include <cmath>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

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
//
// §6.20.2 (printed page 126) gives a parameter with a range specification the
// range of its declaration, and §7.4.1 (printed 153) makes a second packed
// dimension multiply the first, so the declared type is sized against
// `scope`, the parameters already elaborated, and `typedefs`, the scope's
// type names, as ElaborateParamPortList sizes a parameter port. Sized with
// neither, `logic [HI:1][3:0] V` under `localparam int HI = 8` had a
// decl_width of 1, the vector atom's, with HI unfolded, and `logic [HI:1] V`
// was read at the span of its recorded bounds alone, 8 where `[HI:1][3:0]` is
// 32.
void PopulateValueParamInfo(
    RtlirParamDecl& pd, const ModuleItem* item,
    std::unordered_set<std::string_view>& real_param_names,
    const TypedefMap& typedefs, const ScopeMap& scope) {
  PopulateParamTypeInfo(pd, item->data_type, typedefs, scope);
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
  // The parameters already elaborated, which a range bound, a type and the
  // value written in terms of one are each folded against.
  const ScopeMap kScope = BuildParamScope(mod);
  if (!is_type) {
    PopulateValueParamInfo(pd, item, real_param_names_, typedefs_, kScope);
    // §11.5.1: a select on this parameter names bits by their index in the
    // range it is declared with, so keep the two bounds. They are folded
    // against the parameters already elaborated, which is what a bound written
    // in terms of an earlier parameter needs.
    RecordParamDeclRange(pd, item->data_type, kScope);
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
    ResolveParamConstValue(pd, item, is_type, kScope, arena_);
  }
  mod->params.push_back(pd);

  const_names_.insert(item->name);
}

}  // namespace delta
