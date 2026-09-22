#include "simulator/class_specialization.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

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

// §8.25 with §23.10.2.2: a type parameter's actual matches by matching types,
// so the key has to tell two actuals apart exactly when their types differ. A
// named type is told by its name. A built-in one is spelled by its keyword
// together with the width its declaration gives it, which separates integer
// from shortint by the keyword and `bit [2:0]` from `bit [7:0]` by the width,
// whatever name it carries: ParseDataType (parser_types.cpp) records a
// keyword's own text as the name of the type a declaration writes, which
// leaves `bit [2:0]` and `bit [7:0]` both named bit, while the same keyword
// read out of a scope form's list (TypeSpelledBy) carries no name at all, so
// a name taken first keyed a declaration's `C #(byte)` as C#(byte) and the
// scope form `C#(byte)::` as C#(byte[8]), two specializations of one type.
// The declaration's own default stands where the specialization leaves the
// parameter out, which is the type the default specialization binds.
std::string TypeActualKey(const ClassDecl* decl, size_t i,
                          const DataType* actual, SimContext& ctx) {
  const DataType* type = actual;
  if (type == nullptr)
    type = i < decl->param_types.size() ? &decl->param_types[i] : nullptr;
  if (type == nullptr) return {};
  std::string key(BuiltinTypeKeyword(type->kind));
  if (key.empty()) return std::string(type->type_name);
  return key + "[" + std::to_string(DeclaredTypeWidth(*type, ctx)) + "]";
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
void BindSpecializationBase(ClassTypeInfo* spec,
                            const std::vector<DataType>& actuals,
                            SimContext& ctx, Arena& arena) {
  const ClassDecl* decl = spec->decl;
  if (!decl->base_class_type_params.empty() &&
      decl->type_param_names.count(decl->base_class) == 0) {
    // Asked for again by its own name, the copy holding its base for reading
    // alone.
    ClassTypeInfo* base = spec->parent != nullptr
                              ? ctx.FindClassType(spec->parent->name)
                              : nullptr;
    if (base == nullptr) return;
    spec->parent = SpecializationOf(
        base, ActualsUnderSpecialization(spec, decl->base_class_type_params),
        ctx, arena);
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

std::vector<DataType> ActualsUnderSpecialization(
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

ClassTypeInfo* SpecializationOf(ClassTypeInfo* generic,
                                const std::vector<DataType>& actuals,
                                SimContext& ctx, Arena& arena) {
  if (generic == nullptr || generic->decl == nullptr || actuals.empty())
    return generic;
  const ClassDecl* decl = generic->decl;
  std::vector<DataType> spelled = SpelledActuals(decl, actuals);
  // §8.25.1 with §6.20.2: an actual, like a default, is sized by the type the
  // parameter's declaration writes, and a range may name an earlier
  // parameter, so one sizer takes the list in header order and records each
  // value for the ranges after it.
  ClassParamSizer sizer(decl);
  std::string key(generic->name);
  key += "#(";
  std::vector<std::pair<std::string_view, Logic4Vec>> values;
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
  BindSpecializationBase(spec, spelled, ctx, arena);
  for (auto& [pname, value] : values)
    spec->static_properties[std::string(pname)] = value;
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

ClassTypeInfo* ScopeNamedSpecialization(const Expr* base, SimContext& ctx,
                                        Arena& arena) {
  if (base == nullptr || base->kind != ExprKind::kIdentifier) return nullptr;
  ClassTypeInfo* generic = ctx.FindClassType(base->text);
  if (generic == nullptr || generic->decl == nullptr) return nullptr;
  if (base->has_param_spec && !base->elements.empty())
    return SpecializationOf(generic, ScopeActuals(*base), ctx, arena);
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
