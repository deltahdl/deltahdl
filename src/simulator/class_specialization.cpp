#include "simulator/class_specialization.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

// The packed dimensions a type writes, each a left and a right bound, outermost
// first.
using PackedDims = std::vector<std::pair<Expr*, Expr*>>;

// §6.11 and §6.12 name the integral and real types the standard defines, each
// of which a type actual may be written as; the keyword each such kind is
// spelled by in a specialization's key, whatever name the type carries. Empty
// for a kind no type actual is written as -- a net type, a void -- and for the
// named and inline aggregate kinds, which TypeActualKey spells for itself.
std::string_view BuiltinTypeKeyword(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kLogic:
      return "logic";
    case DataTypeKind::kReg:
      return "reg";
    case DataTypeKind::kBit:
      return "bit";
    case DataTypeKind::kByte:
      return "byte";
    case DataTypeKind::kShortint:
      return "shortint";
    case DataTypeKind::kInt:
      return "int";
    case DataTypeKind::kLongint:
      return "longint";
    case DataTypeKind::kInteger:
      return "integer";
    case DataTypeKind::kReal:
      return "real";
    case DataTypeKind::kShortreal:
      return "shortreal";
    case DataTypeKind::kTime:
      return "time";
    case DataTypeKind::kRealtime:
      return "realtime";
    case DataTypeKind::kString:
      return "string";
    case DataTypeKind::kEvent:
      return "event";
    case DataTypeKind::kChandle:
      return "chandle";
    case DataTypeKind::kVoid:
      return "void";
    default:
      return {};
  }
}

// §6.18 with §6.22.1: the built-in type at the end of the chain of typedefs
// the name `type` writes, `int` for `word_t` under `typedef int word_t;`.
// Null where `type` names no typedef, where the chain ends at no built-in
// type -- a class, an enum, a struct -- and where a step on it writes a
// parameter list or declares unpacked dimensions, `typedef int iq_t[$];`
// standing for a queue of int rather than for int. Each packed dimension a
// step writes is appended to `dims`, the use-site's ahead of the typedef's,
// since §7.4.4 stacks a dimension written where the name is used outside the
// ones the typedef carries.
const DataType* BuiltinTypedefTarget(const DataType& type, SimContext& ctx,
                                     PackedDims& dims) {
  const DataType* step = &type;
  for (size_t hops = 0; hops <= ctx.TypeDeclarationCount(); ++hops) {
    if (step->packed_dim_left != nullptr) {
      dims.emplace_back(step->packed_dim_left, step->packed_dim_right);
      dims.insert(dims.end(), step->extra_packed_dims.begin(),
                  step->extra_packed_dims.end());
    }
    if (step->kind != DataTypeKind::kNamed)
      return BuiltinTypeKeyword(step->kind).empty() ? nullptr : step;
    if (!step->type_params.empty()) return nullptr;
    const ModuleItem* item = TypedefItemSeenFrom(*step, nullptr, ctx);
    if (item == nullptr || !item->unpacked_dims.empty()) return nullptr;
    step = &item->typedef_type;
  }
  return nullptr;
}

// §6.11 (printed page 109): whether the integral built-in `kind` is
// 4-state, and the width it is predefined to have, 0 for bit, logic and reg,
// which take theirs from their packed dimensions; §6.11.2 makes logic and reg
// one type. Nullopt for a kind that is no integral built-in type.
std::optional<std::pair<bool, uint32_t>> IntegralKindForm(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
      return std::pair{false, 0u};
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return std::pair{true, 0u};
    case DataTypeKind::kByte:
      return std::pair{false, 8u};
    case DataTypeKind::kShortint:
      return std::pair{false, 16u};
    case DataTypeKind::kInt:
      return std::pair{false, 32u};
    case DataTypeKind::kLongint:
      return std::pair{false, 64u};
    case DataTypeKind::kInteger:
      return std::pair{true, 32u};
    case DataTypeKind::kTime:
      return std::pair{true, 64u};
    default:
      return std::nullopt;
  }
}

// §7.4.1 with §6.22.1: the bounds of the packed dimensions `dims` lists,
// outermost first, each spelled "[left:right]". Nullopt where a bound cannot be
// folded here or the bounds do not account for the `width` bits the type was
// sized with, as RecordPackedRange (lowerer_register.cpp) declines such bounds
// for a variable; the caller then spells the type by its width alone.
std::optional<std::string> PackedBoundsKey(const PackedDims& dims,
                                           uint32_t width, SimContext& ctx) {
  std::string key;
  uint64_t bits = 1;
  for (const auto& [left, right] : dims) {
    if (left == nullptr || right == nullptr) return std::nullopt;
    Logic4Vec lv = EvalExpr(left, ctx, ctx.GetArena());
    Logic4Vec rv = EvalExpr(right, ctx, ctx.GetArena());
    if (HasUnknownBits(lv) || HasUnknownBits(rv)) return std::nullopt;
    int64_t l = SelectBoundValue(lv);
    int64_t r = SelectBoundValue(rv);
    bits *= static_cast<uint64_t>((l >= r ? l - r : r - l) + 1);
    key += "[" + std::to_string(l) + ":" + std::to_string(r) + "]";
  }
  if (bits != width) return std::nullopt;
  return key;
}

// §6.22.1 (printed page 135): an integral built-in type spelled by what makes
// two such types match -- 2- or 4-state, signed or not, and the bounds of each
// packed dimension -- as the simple bit vector it matches, rule e) spelling a
// type with a predefined width as the vector ranged [width-1:0] and rule g)
// taking the signing a type ends with, however written. So `byte` and `bit
// signed [7:0]` are both "bit signed[7:0]", `integer` and `logic signed
// [31:0]` both "logic signed[31:0]", and `bit [2:0]` and `bit [3:1]`, which
// rule f) keeps apart by their bounds, two keys. A scalar is the vector ranged
// [0:0], and a type nothing sizes is spelled with no bounds. `form` is the
// state and predefined width IntegralKindForm answers for `builtin`'s kind.
std::string IntegralTypeKey(const DataType& builtin,
                            std::pair<bool, uint32_t> form,
                            const PackedDims& dims, uint32_t width,
                            SimContext& ctx) {
  const auto [four_state, predefined] = form;
  std::string key = four_state ? "logic" : "bit";
  if (builtin.is_signed) key += " signed";
  if (width == 0) return key;
  std::optional<std::string> bounds;
  if (predefined == 0) bounds = PackedBoundsKey(dims, width, ctx);
  if (!bounds.has_value() || bounds->empty())
    bounds = "[" + std::to_string(width - 1) + ":0]";
  return key + *bounds;
}

// §8.25 with §23.10.2.2: a type parameter's actual matches by matching types,
// so the key has to tell two actuals apart exactly when their types differ. A
// named type is told by its name. A built-in one is spelled as §6.22.1 matches
// it (IntegralTypeKey), whatever name it carries: ParseDataType
// (parser_types.cpp) records a keyword's own text as the name of the type a
// declaration writes, while the same keyword read out of a scope form's list
// (TypeSpelledBy) carries no name at all, so a name taken first keyed a
// declaration's `C #(byte)` and the scope form `C#(byte)::` as two
// specializations of one type. The declaration's own default stands where the
// specialization leaves the parameter out, which is the type the default
// specialization binds.
//
// §6.22.1 also makes a typedef name match the type it stands for, so a name
// reaching a built-in type through its chain of typedefs (BuiltinTypedefTarget)
// is spelled as that type is: keyed by the alias's own name, `S #(word_t)`
// under `typedef int word_t;` was a specialization apart from `S #(int)`, with
// statics of its own. Keyed by keyword and width, `C #(bit signed [7:0])` was
// apart from `C #(byte)`, and `C #(bit [2:0])` one with `C #(bit [3:1])`. A
// built-in type that is not integral is spelled by its keyword, realtime as
// real, the two being one type (§6.12, printed page 110).
std::string TypeActualKey(const ClassDecl* decl, size_t i,
                          const DataType* actual, SimContext& ctx) {
  const DataType* type = actual;
  if (type == nullptr)
    type = i < decl->param_types.size() ? &decl->param_types[i] : nullptr;
  if (type == nullptr) return {};
  PackedDims dims;
  const DataType* builtin = BuiltinTypedefTarget(*type, ctx, dims);
  if (builtin == nullptr) return std::string(type->type_name);
  if (const auto kForm = IntegralKindForm(builtin->kind)) {
    return IntegralTypeKey(*builtin, *kForm, dims,
                           DeclaredTypeWidth(*type, ctx), ctx);
  }
  if (builtin->kind == DataTypeKind::kRealtime) return "real";
  return std::string(BuiltinTypeKeyword(builtin->kind));
}

// §23.10.2.2 with §8.25.1: the `#(...)` of a scope form is a parameter value
// assignment list, which the parser leaves on the identifier as expressions in
// `elements`, each named entry carrying its parameter's name in `arg_names`.
// SpecializationOf reads the actuals a variable's declaration gives it, where
// the expression stands under `type_ref_expr` and the name under
// `param_arg_name`, so the list is rewritten into that shape.
std::vector<DataType> ScopeActuals(const Expr& base) {
  std::vector<DataType> actuals(base.elements.size());
  for (size_t i = 0; i < base.elements.size(); ++i) {
    actuals[i].type_ref_expr = base.elements[i];
    if (i < base.arg_names.size())
      actuals[i].param_arg_name = base.arg_names[i];
  }
  return actuals;
}

// §8.25 (printed page 204 of IEEE 1800-2023): the extends clause of a
// parameterized class may name one of the class's own type parameters, `class
// D #(type B = P) extends B;`. This is the actual `actuals` binds that
// parameter to; null where the extends clause names no type parameter of the
// class, and where the list leaves that parameter out, which leaves the
// parameter's default standing.
const DataType* BaseActual(const ClassDecl* decl,
                           const std::vector<DataType>& actuals) {
  if (decl->base_class.empty() ||
      decl->type_param_names.count(decl->base_class) == 0) {
    return nullptr;
  }
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == decl->base_class)
      return ActualForParam(actuals, i, decl->base_class);
  }
  return nullptr;
}

// §8.25: the type the specialization `holder` binds its own type parameter
// `pname` to, null where it binds it nothing -- the class declaration's own
// type, which §8.25.1 makes the default specialization, binds none.
const DataType* HolderActualFor(const ClassTypeInfo* holder,
                                std::string_view pname) {
  if (holder->param_actuals == nullptr) return nullptr;
  const ClassDecl* decl = holder->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == pname)
      return ActualForParam(*holder->param_actuals, i, pname);
  }
  return nullptr;
}

// §8.3 with §8.23: a class-scope typedef is an item of the class declaring
// it, so a name one names in an actual list the class `holder` writes -- UVM's
// `this_type` in uvm_object_registry#(T,Tname)'s `typedef
// uvm_registry_common#(this_type, ...) common_type;` -- denotes the class that
// typedef names in `holder`, or in a base `holder` inherits it from (§8.13).
// The class the run holds under `holder`'s own name for it, null where
// `actual` writes a list of its own or names no such typedef. Kept by the bare
// name, the actual was read again in the scope of the class it specializes,
// where the same name is that class's own typedef: uvm_registry_common's
// Tregistry named uvm_registry_common itself, and Tregistry::get() answered no
// registry.
const ClassTypeInfo* HolderScopeClass(const ClassTypeInfo* holder,
                                      const DataType& actual, SimContext& ctx) {
  if (!actual.type_params.empty() || !actual.scope_name.empty()) return nullptr;
  for (const ClassTypeInfo* level = holder; level != nullptr;
       level = level->parent) {
    if (const ClassTypeInfo* cls = ctx.FindClassType(
            std::string(level->name) + "::" + std::string(actual.type_name)))
      return cls;
  }
  return nullptr;
}

// §8.3 with §6.18: an actual naming a class-scope typedef of `holder` that
// stands for no class -- UVM's `rsrc_sv_q_t` in uvm_resource_types's `typedef
// uvm_shared#(rsrc_sv_q_t) rsrc_shared_q_t;`, a queue of uvm_resource_base --
// names the type that typedef declares in `holder`, so the actual is
// qualified with `holder`'s name, where TypedefItemSeenFrom
// (eval_array_class_assoc.h) finds it. Left bare, the name was looked up
// from the specialized class, which declares no such typedef, and uvm_shared's
// `T value` lost the queue dimension.
void QualifyHolderTypedef(const ClassTypeInfo* holder, DataType& actual) {
  if (!actual.type_params.empty() || !actual.scope_name.empty()) return;
  if (ClassScopeTypedefItem(holder, actual.type_name) == nullptr) return;
  actual.scope_name = holder->name;
}

// §8.25: the name of the generic class the class named `name` specializes,
// the part of a specialization's name ahead of the `#(` SpecializationOf
// appends its list after; `name` itself for a class that is no
// specialization.
std::string_view GenericNameOf(std::string_view name) {
  return name.substr(0, name.find("#("));
}

// §8.25: the class `spec` extends, where its declaration's extends clause
// names one of the class's own type parameters, is the one this set of actuals
// binds that parameter to. BaseClassOf in lowerer_class.cpp binds the
// declaration's base from the parameter's default, there being one
// ClassTypeInfo per declaration when it runs, and that default is the base of
// §8.25.1's default specialization alone; the copy a specialization is made of
// carries it until this answers the actual's class instead. An actual that is
// no named type, and one naming no class, leave the default standing.
//
// Where the extends clause writes a `#(...)` list instead, `class D3 #(type P
// = real) extends C #(P);` (printed page 204 of IEEE 1800-2023), what it
// names is a specialization of the base, C#(P) binding C's T to P, and the
// class `spec` extends is that specialization with each of the class's own
// parameters the list names replaced by the type `spec` binds it to. The copy
// carries the base's declaration, whose static member variables are the
// default specialization's, so a static property the base declares -- UVM's
// `static this_type m_t_inst` in uvm_typed_callbacks#(T), which
// uvm_callbacks#(T,CB) extends -- was read off a copy that
// uvm_typed_callbacks#(T)'s own static methods never wrote.
// §8.13 with §8.25: the specialization of `base` that the extends clause of
// `info` names. A value actual may name one of the class's own value
// parameters, `extends Mem #(.K(W))`, which stands for the value `info` binds
// it to -- its declaration's default for the class itself, the actual for a
// specialization of it -- so those values are bound in a scope of their own
// while the list is read. Read with nothing bound, `G #(8)`'s base was Mem
// #(0).
ClassTypeInfo* BaseUnderOwnParams(const ClassTypeInfo* info,
                                  ClassTypeInfo* base, SimContext& ctx,
                                  Arena& arena) {
  const ClassDecl* decl = info->decl;
  if (!info->package.empty()) ctx.PushScope(info->package);
  ctx.PushScope();
  for (const auto& [pname, pexpr] : decl->params) {
    if (decl->type_param_names.count(pname) != 0) continue;
    auto entry = info->static_properties.find(std::string(pname));
    if (entry == info->static_properties.end()) continue;
    ctx.CreateLocalVariable(pname, entry->second.width)->value = entry->second;
  }
  ClassTypeInfo* spec = SpecializationOf(
      base, ActualsUnderSpecialization(info, decl->base_class_type_params, ctx),
      ctx, arena);
  ctx.PopScope();
  if (!info->package.empty()) ctx.PopScope();
  return spec;
}

void BindSpecializationBase(ClassTypeInfo* spec,
                            const std::vector<DataType>& actuals,
                            SimContext& ctx, Arena& arena) {
  const ClassDecl* decl = spec->decl;
  if (!decl->base_class_type_params.empty() &&
      decl->type_param_names.count(decl->base_class) == 0) {
    // Asked for again by its generic's name, the copy holding its base for
    // reading alone, and the base BindDeclarationBase gave the declaration
    // being a specialization already, named by the generic's name and its
    // list.
    ClassTypeInfo* base =
        spec->parent != nullptr
            ? ctx.FindClassType(GenericNameOf(spec->parent->name))
            : nullptr;
    if (base == nullptr) return;
    spec->parent = BaseUnderOwnParams(spec, base, ctx, arena);
    return;
  }
  const DataType* actual = BaseActual(decl, actuals);
  if (actual == nullptr || actual->kind != DataTypeKind::kNamed) return;
  if (ClassTypeInfo* base = ctx.FindClassType(actual->type_name))
    spec->parent = base;
}

// §8.25 with §23.10.2.2: a type parameter's actual matches another by
// matching types, so each type actual is held as the type it spells. A scope
// form's list, `C#(byte)::`, reaches here through ScopeActuals as the
// expressions the parser left, each an implicit type carrying the element
// that spells it, and a declaration's list leaves a name the parser did not
// read as a type the same way (ParseOneTypeParam in parser_types.cpp).
// Spelled by no name and an implicit kind, every such actual keyed alike, so
// C#(byte):: and C#(shortint):: were one specialization with one set of
// static member variables, and neither was the C#(byte) a declaration
// writes, which the parser reads as the keyword's type. A value parameter's
// actual is an expression and stays one.
std::vector<DataType> SpelledActuals(const ClassDecl* decl,
                                     const std::vector<DataType>& actuals) {
  std::vector<DataType> spelled = actuals;
  for (size_t j = 0; j < spelled.size(); ++j) {
    DataType& actual = spelled[j];
    std::string_view pname = actual.param_arg_name;
    if (pname.empty() && j < decl->params.size()) pname = decl->params[j].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    if (actual.kind != DataTypeKind::kImplicit ||
        actual.type_ref_expr == nullptr) {
      continue;
    }
    DataType type = TypeSpelledBy(actual.type_ref_expr);
    if (type.kind == DataTypeKind::kImplicit) continue;
    type.param_arg_name = actual.param_arg_name;
    actual = type;
  }
  return spelled;
}

}  // namespace

const DataType* RunningTypeActual(std::string_view name, SimContext& ctx) {
  const ClassTypeInfo* running = ctx.CurrentMethodClass();
  if (running == nullptr || running->decl == nullptr ||
      running->decl->type_param_names.count(name) == 0) {
    return nullptr;
  }
  if (const DataType* bound = ctx.FindScopeTypeActual(name)) return bound;
  if (const DataType* actual = HolderActualFor(running, name)) return actual;
  const ClassObject* self = ctx.CurrentThis();
  bool own = self != nullptr && self->type != nullptr &&
             self->type->decl == running->decl;
  return TypeParamActual(own ? self : nullptr, running->decl, name);
}

namespace {

// §8.25 (printed page 204 of IEEE 1800-2023): a type parameter used in a type
// resolves to a type only after elaboration, so a scope form written in a
// method of a parameterized class whose list names that class's own type
// parameter -- UVM's `uvm_typeid#(CB)::get()` in uvm_callbacks#(T,CB) --
// names the specialization of `decl` the running specialization's actual
// gives, a different one under each specialization of the running class.
// These are the actuals `written` spells, each naming such a parameter
// replaced by the type RunningTypeActual answers for it; spelled by the name
// alone, every such scope keyed by the parameter's name, and one
// specialization answered for every T.
std::vector<DataType> ActualsUnderRunningClass(
    const ClassDecl* decl, const std::vector<DataType>& written,
    SimContext& ctx) {
  std::vector<DataType> bound = SpelledActuals(decl, written);
  for (DataType& actual : bound) {
    if (actual.kind != DataTypeKind::kNamed) continue;
    const DataType* a = RunningTypeActual(actual.type_name, ctx);
    if (a == nullptr) continue;
    std::string_view arg = actual.param_arg_name;
    actual = *a;
    actual.param_arg_name = arg;
  }
  return bound;
}

}  // namespace

std::vector<DataType> ActualsUnderSpecialization(
    const ClassTypeInfo* holder, const std::vector<DataType>& written,
    SimContext& ctx) {
  std::vector<DataType> bound = written;
  for (DataType& actual : bound) {
    if (actual.kind != DataTypeKind::kNamed) continue;
    if (holder->decl->type_param_names.count(actual.type_name) == 0) {
      if (const ClassTypeInfo* cls = HolderScopeClass(holder, actual, ctx))
        actual.type_name = cls->name;
      else
        QualifyHolderTypedef(holder, actual);
      continue;
    }
    const DataType* a = HolderActualFor(holder, actual.type_name);
    // §8.25.1: the generic class stands for the default specialization, so
    // with no actuals of its own its parameter is its default, which UVM's
    // `typedef uvm_resource #(T) rsrc_t;` in uvm_resource_db_implementation_t
    // #(type T = uvm_object) writes. Left as the bare name, the list spelled
    // a specialization keyed by `T` that no other name reached.
    if (a == nullptr && holder->param_actuals == nullptr)
      a = TypeParamActual(nullptr, holder->decl, actual.type_name);
    if (a == nullptr) continue;
    std::string_view arg = actual.param_arg_name;
    actual = *a;
    actual.param_arg_name = arg;
  }
  return bound;
}

ClassTypeInfo* ClassNamedByTypeParam(std::string_view name, SimContext& ctx,
                                     Arena& arena) {
  const DataType* actual = RunningTypeActual(name, ctx);
  if (actual == nullptr || actual->kind != DataTypeKind::kNamed) return nullptr;
  ClassTypeInfo* generic = nullptr;
  if (!actual->scope_name.empty()) {
    generic = ctx.FindClassType(std::string(actual->scope_name) +
                                "::" + std::string(actual->type_name));
  }
  if (generic == nullptr) generic = ctx.FindClassType(actual->type_name);
  if (generic == nullptr) return nullptr;
  return SpecializationOf(generic, actual->type_params, ctx, arena);
}

namespace {

using ParamValues = std::vector<std::pair<std::string_view, Logic4Vec>>;

// The key SpecializationOf registers the specialization of `generic` that
// `spelled` names under, `vector#(4)`, with the value each value parameter
// takes collected into `values`. An empty list spells the declaration's
// defaults.
std::string SpecializationKey(const ClassTypeInfo* generic,
                              const std::vector<DataType>& spelled,
                              SimContext& ctx, Arena& arena,
                              ParamValues& values) {
  const ClassDecl* decl = generic->decl;
  // §8.25.1 with §6.20.2: an actual, like a default, is sized by the type the
  // parameter's declaration writes, and a range may name an earlier
  // parameter, so one sizer takes the list in header order and records each
  // value for the ranges after it.
  ClassParamSizer sizer(decl);
  std::string key(generic->name);
  key += "#(";
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (i != 0) key += ",";
    std::string_view pname = decl->params[i].first;
    // §23.10.2.2 through §8.25: an actual is matched to its parameter by the
    // name it was written with, in the named form, and otherwise by position.
    const DataType* actual = ActualForParam(spelled, i, pname);
    if (decl->type_param_names.count(pname) != 0) {
      key += TypeActualKey(decl, i, actual, ctx);
      continue;
    }
    const Expr* expr = actual != nullptr && actual->type_ref_expr != nullptr
                           ? actual->type_ref_expr
                           : decl->params[i].second;
    // A parameter the declaration gives no default and the specialization no
    // actual has no value to spell; §8.25 makes such a class one every
    // specialization must override, and 0 is what the lowerer stores for it.
    Logic4Vec value = expr != nullptr ? sizer.Value(i, expr, ctx, arena)
                                      : MakeLogic4VecVal(arena, 32, 0);
    // The low 64 bits spell the value in the key. Two specializations whose
    // parameters agree there and differ above it would share a key; every
    // parameter deltahdl sizes today fits, and the alternative spelling costs
    // the readable name §37.32 asks a specialization to carry.
    key += std::to_string(value.ToUint64());
    values.emplace_back(pname, value);
  }
  key += ")";
  return key;
}

// §8.25 with §8.20: a virtual method an object of `spec` dispatches to is a
// method of `spec`, or of the base level of `spec` that declares it, and runs
// as that class's, with its type parameters, its class-scope typedefs and its
// statics. The vtable copied from the declaration names the generic class
// and the generic bases as the owners, so each entry is moved to the level
// of `spec`'s chain made from the same declaration. Left on the declaration,
// uvm_resource_db_default_implementation_t #(T)'s get_by_name ran under the
// generic class, and the `rsrc_t::get_type()` it passed was another
// specialization's handle than the one every stored resource reported.
void OwnVTableEntries(ClassTypeInfo* spec) {
  for (VTableEntry& entry : spec->vtable) {
    if (entry.owner == nullptr) continue;
    for (const ClassTypeInfo* level = spec; level != nullptr;
         level = level->parent) {
      if (level->decl == entry.owner->decl) {
        entry.owner = level;
        break;
      }
    }
  }
}

// §8.25 with §23.10.2.2: the actual `actuals` gives the type parameter `name`
// of `decl`, null where the list leaves it at its default or `decl` declares
// no parameter of that name.
const DataType* TypeParamActualIn(const ClassDecl* decl,
                                  const std::vector<DataType>& actuals,
                                  std::string_view name) {
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == name) return ActualForParam(actuals, i, name);
  }
  return nullptr;
}

// Whether `actual` sizes a property as one integral value: not a string, not
// a real, and no typedef with unpacked dimensions, which #4367 makes a queue or
// array property.
bool ActualSizesIntegralProperty(const DataType& actual, SimContext& ctx) {
  if (DeclaredTypeIsString(actual, ctx) || DeclaredTypeIsReal(actual, ctx))
    return false;
  if (actual.kind != DataTypeKind::kNamed) return true;
  const ModuleItem* item = ctx.FindTypedefItem(actual.type_name);
  return item == nullptr || item->unpacked_dims.empty();
}

// §8.25 (printed pages 203-204) with §6.20.3 (printed page 128): a property
// whose declared type is a type parameter of the class, `T value`, is declared
// with the type the specialization's actual names, so `value` of
// `S #(bit [7:0])` is an 8-bit variable. The declaration's property table,
// which the specialization copies, sizes such a property with the 32-bit
// carrier its collector gives any name and leaves its width undeclared, so a
// write kept all 32 bits of 300 where §10.7 keeps 8, and `$bits` answered 32.
// The specialization's own table takes the actual's width and signedness, and
// its state-ness where the actual is written as a keyword type rather than a
// name. An actual this cannot size as one integral value -- a string, a real,
// a class, a typedef with unpacked dimensions -- leaves the property as the
// declaration sized it.
void SizeTypeParamProperties(ClassTypeInfo* spec,
                             const std::vector<DataType>& actuals,
                             SimContext& ctx) {
  const ClassDecl* decl = spec->decl;
  for (auto& prop : spec->properties) {
    std::string_view pname = prop.type_name.empty()
                                 ? std::string_view{}
                                 : TypeParamNamedBy(decl, prop.type_name);
    if (prop.width_is_declared || pname.empty()) continue;
    const DataType* actual = TypeParamActualIn(decl, actuals, pname);
    if (actual == nullptr || !ActualSizesIntegralProperty(*actual, ctx))
      continue;
    uint32_t width = DeclaredTypeWidth(*actual, ctx);
    if (width == 0) continue;
    prop.width = width;
    prop.width_is_declared = true;
    prop.is_signed = DeclaredTypeIsSigned(*actual, ctx);
    if (actual->kind != DataTypeKind::kNamed)
      prop.is_4state = DeclaredTypeIs4State(*actual, ctx);
  }
}

// §6.20.1: the property `name` the class body of `decl` declares, null where
// it declares none; a parameter carried as a property member (is_param) is no
// property.
const ClassMember* DeclaredProperty(const ClassDecl* decl,
                                    std::string_view name) {
  for (const auto* m : decl->members) {
    if (m->kind == ClassMemberKind::kProperty && !m->is_param &&
        m->name == name)
      return m;
  }
  return nullptr;
}

// §8.25 with §7.4.1: the constants a property's packed dimension folds against
// under the specialization `spec` -- the compilation unit's, the value each of
// its header parameters takes (`values`), and then the parameters of the
// class body, which may name them (§6.20.1) -- as ClassParamScope in
// lowerer_class.cpp gathers them at the declaration's defaults.
ScopeMap SpecializationParamScope(const ClassTypeInfo* spec,
                                  const ParamValues& values) {
  ScopeMap scope;
  if (spec->unit_constants != nullptr) scope = *spec->unit_constants;
  for (const auto& [pname, value] : values)
    scope[pname] = SelectBoundValue(value);
  for (const auto* member : spec->decl->members) {
    if (member->kind != ClassMemberKind::kProperty || !member->is_param ||
        member->init_expr == nullptr) {
      continue;
    }
    if (auto v = ConstEvalInt(member->init_expr, scope))
      scope[member->name] = *v;
  }
  return scope;
}

// §8.23: a property declared by `type`, the bare name of a structure or union
// typedef the class declares, holds the layout that typedef has under the
// specialization `spec`, folded with its values `scope` and registered under
// its own key, `Box#(16)::S`, which `prop` takes with the layout's width.
// False for a property declared by any other type.
bool SizeClassTypedefProperty(ClassTypeInfo::PropertyInfo& prop,
                              const DataType& type, const ClassTypeInfo* spec,
                              const ScopeMap& scope, SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return false;
  const DataType* aggregate =
      ClassAggregateTypedef(*spec->decl, type.type_name);
  if (aggregate == nullptr) return false;
  std::string_view key = RegisterSpecializationTypedefLayout(
      spec->name, type.type_name, *aggregate, scope, ctx);
  if (const StructTypeInfo* layout = ctx.FindStructType(key)) {
    prop.type_name = key;
    prop.width = layout->total_width;
    prop.width_is_declared = true;
  }
  return true;
}

// §8.13 with §8.23 and §8.25: the key of the layout a property of the
// specialization `spec`, declared by `type`, holds where `type` is the bare
// name of a structure or union typedef a base class with value parameters
// declares: the layout under the base specialization `spec` extends,
// `Base#(4)::S` for `D #(4)` extending `Base #(N)`. Empty for any other type.
std::string_view BaseTypedefKey(const DataType& type, const ClassTypeInfo& spec,
                                SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty()) return {};
  const ClassDecl* decl = nullptr;
  const ClassTypeInfo* owner =
      ClassTypedefDeclarer(type.type_name, spec, *spec.decl, decl);
  if (owner == nullptr || owner == &spec || !ClassHasValueParams(*decl))
    return {};
  const DataType* aggregate = ClassAggregateTypedef(*decl, type.type_name);
  if (aggregate == nullptr) return {};
  return ClassTypedefLayoutKey(*owner, type.type_name, *aggregate, ctx);
}

// A property of `spec` declared by a parameterized base's typedef takes the
// layout that typedef has under the base `spec` extends (BaseTypedefKey),
// which is known only once the base is bound, and that layout's width.
void SizeBaseTypedefProperties(ClassTypeInfo* spec, SimContext& ctx) {
  for (auto& prop : spec->properties) {
    const ClassMember* member = DeclaredProperty(spec->decl, prop.name);
    if (member == nullptr) continue;
    std::string_view key = BaseTypedefKey(member->data_type, *spec, ctx);
    const StructTypeInfo* layout =
        key.empty() ? nullptr : ctx.FindStructType(key);
    if (layout == nullptr) continue;
    prop.type_name = key;
    prop.width = layout->total_width;
    prop.width_is_declared = true;
  }
}

// §8.25 (printed page 203): a property whose packed dimension names a value
// parameter, the clause's `bit [size-1:0] a`, is as wide as the
// specialization binds the parameter, ten bits in `vector #(10)`. The table a
// specialization copies was sized at the declaration's defaults
// (CollectClassMembers in lowerer_class.cpp), which are the default
// specialization's (§8.25.1), so `logic [W-1:0] v` stayed 8 bits under
// `C #(16)`. Each property the class declares is folded again with the
// specialization's own values; one whose type does not fold -- a name, a type
// parameter, which SizeTypeParamProperties sizes -- is left as it was.
//
// §7.4.2 with §8.25: a fixed unpacked dimension naming one, `int g[N]`, is
// folded again the same way, so `Box #(string, 6)` holds six elements where
// the default specialization holds three.
void SizeValueParamProperties(ClassTypeInfo* spec, const ParamValues& values,
                              SimContext& ctx, Arena& arena) {
  if (values.empty()) return;
  ScopeMap scope = SpecializationParamScope(spec, values);
  for (auto& prop : spec->properties) {
    const ClassMember* member = DeclaredProperty(spec->decl, prop.name);
    if (member == nullptr) continue;
    if (prop.array_size > 0 && member->unpacked_dims.size() == 1) {
      PropertyArrayDim dim =
          FoldPropertyDimension(member->unpacked_dims[0], scope, ctx, arena);
      if (dim.size > 0) prop.array_size = dim.size;
    }
    if (SizeClassTypedefProperty(prop, member->data_type, spec, scope, ctx))
      continue;
    uint32_t width = EvalTypeWidth(member->data_type, {}, scope);
    if (width == 0) continue;
    prop.width = width;
    prop.width_is_declared = true;
  }
}

}  // namespace

// §7.4.2 with §23.9: a size `scope` does not fold, `[K]` or `[P * 2]` naming
// a parameter of the module the class is declared in, as the running scope
// reads it; nothing for a name no variable of that scope answers, which is
// how an associative array's index type or a type parameter, `[T]`, is
// written, and nothing where the value is unknown.
static std::optional<int64_t> RunningScopeSize(const Expr* dim, SimContext& ctx,
                                               Arena& arena) {
  bool readable = dim->kind == ExprKind::kIdentifier
                      ? ctx.FindVariable(dim->text) != nullptr
                      : dim->kind == ExprKind::kBinary;
  if (!readable) return std::nullopt;
  Logic4Vec value = EvalExpr(dim, ctx, arena);
  if (!value.IsKnown()) return std::nullopt;
  return static_cast<int64_t>(value.ToUint64());
}

PropertyArrayDim FoldPropertyDimension(const Expr* dim, const ScopeMap& scope,
                                       SimContext& ctx, Arena& arena) {
  if (dim == nullptr) return {};
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon ||
      dim->lhs == nullptr || dim->rhs == nullptr) {
    std::optional<int64_t> size = ConstEvalInt(dim, scope);
    if (!size) size = RunningScopeSize(dim, ctx, arena);
    if (!size || *size <= 0) return {};
    return {static_cast<uint32_t>(*size), 0, false};
  }
  auto bound = [&](const Expr* e) {
    if (auto v = ConstEvalInt(e, scope)) return *v;
    return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
  };
  int64_t left = bound(dim->lhs);
  int64_t right = bound(dim->rhs);
  if (left < right) {
    return {static_cast<uint32_t>(right - left + 1), left, false};
  }
  return {static_cast<uint32_t>(left - right + 1), right, left > right};
}

ClassTypeInfo* SpecializationOf(ClassTypeInfo* generic,
                                const std::vector<DataType>& actuals,
                                SimContext& ctx, Arena& arena) {
  if (generic == nullptr || generic->decl == nullptr || actuals.empty())
    return generic;
  std::vector<DataType> spelled = SpelledActuals(generic->decl, actuals);
  ParamValues values;
  std::string key = SpecializationKey(generic, spelled, ctx, arena, values);
  // §8.25 (printed pages 203-204): actuals that match the declaration's
  // defaults parameter for parameter name the default specialization, which
  // §8.25.1 makes the one the unadorned name and `#()` name, so `S #(int)`
  // under `type T = int` is S itself, its static member variables included.
  // Made as a type of its own, `S #(int)::n` read none of what `S s = new;`
  // had counted.
  ParamValues default_values;
  if (key == SpecializationKey(generic, {}, ctx, arena, default_values))
    return generic;
  if (ClassTypeInfo* found = ctx.FindClassType(key)) return found;
  // The declaration's type is copied rather than built again: the interfaces,
  // the members, the vtable and the methods are facts about the declaration
  // and are shared by every specialization, and only the static storage, the
  // parameters standing in it, the actuals themselves and a base the actuals
  // name are the specialization's own.
  auto* spec = arena.Create<ClassTypeInfo>(*generic);
  spec->name = *arena.Create<std::string>(std::move(key));
  // §8.25: the actuals are a fact about the specialization, which is the
  // type, rather than about the declaration each object of it is constructed
  // on, so the list is kept here; copied into the arena because a caller may
  // have built it for the call alone (ScopeActuals above). Construction reads
  // it where the name the `new` was written against carries no list of its
  // own (BindTypeParamActuals in eval_class_params.cpp).
  spec->param_actuals = arena.Create<std::vector<DataType>>(spelled);
  SizeTypeParamProperties(spec, spelled, ctx);
  SizeValueParamProperties(spec, values, ctx, arena);
  // The values are the specialization's before its base is bound, since an
  // extends clause's list may name them, `extends Mem #(.K(W))`.
  for (auto& [pname, value] : values)
    spec->static_properties[std::string(pname)] = value;
  BindSpecializationBase(spec, spelled, ctx, arena);
  SizeBaseTypedefProperties(spec, ctx);
  OwnVTableEntries(spec);
  // §6.20.4 with §8.25: the body's parameters are the specialization's too,
  // `C#(4)::N` 8 where the declaration's copy, folded with W's default, is 16.
  FoldClassBodyParams(generic->decl, ClassStaticLookup(spec),
                      ClassStaticStore(spec), ctx, arena);
  ctx.RegisterClassType(spec->name, spec);
  // §8.25: a class-scope typedef whose actuals name a type parameter of this
  // class resolves to a type only once the actuals are known, so the aliases
  // are bound again under the specialization's own name, `Reg#(byte)::box_t`
  // standing beside the `Reg::box_t` the declaration bound with the parameter
  // standing for nothing. SimContext::FindClassType tries the running
  // method's class before any other, so a method of the specialization
  // reaches its own. Registered ahead of this, so a typedef naming this very
  // specialization -- `typedef Reg#(T) this_type;` -- finds it by its key
  // rather than making it again without end.
  RegisterClassScopeTypedefAliases(spec, ctx, arena);
  InitSpecializationStaticProperties(spec, ctx, arena);
  return spec;
}

void BindDeclarationBase(ClassTypeInfo* info, SimContext& ctx, Arena& arena) {
  const ClassDecl* decl = info->decl;
  if (decl == nullptr || info->parent == nullptr ||
      decl->base_class_type_params.empty() ||
      decl->type_param_names.count(decl->base_class) != 0) {
    return;
  }
  ClassTypeInfo* base = ctx.FindClassType(info->parent->name);
  if (base == nullptr) return;
  ClassTypeInfo* spec = BaseUnderOwnParams(info, base, ctx, arena);
  if (spec == nullptr || spec == base) return;
  info->parent = spec;
  // The vtable was built against the generic base, so an entry the base
  // declares is re-owned by the specialization, whose statics its body then
  // reads.
  OwnVTableEntries(info);
  // §8.25: so were the properties the base's typedefs declare, which take the
  // widths of the specialization the class extends, `Base#(16)::S`.
  SizeBaseTypedefProperties(info, ctx);
}

ClassTypeInfo* ScopeNamedSpecialization(const Expr* base, SimContext& ctx,
                                        Arena& arena) {
  if (base == nullptr || base->kind != ExprKind::kIdentifier) return nullptr;
  ClassTypeInfo* generic = ctx.FindClassType(base->text);
  if (generic == nullptr || generic->decl == nullptr) return nullptr;
  if (base->has_param_spec && !base->elements.empty()) {
    return SpecializationOf(
        generic,
        ActualsUnderRunningClass(generic->decl, ScopeActuals(*base), ctx), ctx,
        arena);
  }
  // §8.25.1: the unadorned name is a legal scope prefix only inside the class
  // it names, and there it refers to the members of the class in hand rather
  // than denoting the default specialization, so it names whichever
  // specialization the running method belongs to. That class is told from an
  // unrelated one of the name by sharing the declaration the bare name found,
  // every specialization being a copy of it; it is asked for again by its own
  // name because the stack hands it out for reading alone.
  const ClassTypeInfo* running = ctx.CurrentMethodClass();
  if (running == nullptr || running->decl != generic->decl) return nullptr;
  return ctx.FindClassType(running->name);
}

bool TryScopeSpecializationStaticMember(const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const ClassTypeInfo* spec = ScopeNamedSpecialization(expr->lhs, ctx, arena);
  if (spec == nullptr) return false;
  // §8.13: the property may be one a base declares, and a base's one storage
  // is where it lives, so the walk that finds the declaring level is asked
  // rather than the specialization's own map.
  const ClassTypeInfo* declarer = spec->StaticPropertyDeclarer(expr->rhs->text);
  if (declarer == nullptr) return false;
  out = declarer->static_properties.find(std::string(expr->rhs->text))->second;
  return true;
}

}  // namespace delta
