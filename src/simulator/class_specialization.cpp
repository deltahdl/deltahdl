#include "simulator/class_specialization.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// §8.25: a type parameter's actual matches by matching types, so the type's
// name is what the key carries for it. The declaration's own default stands
// where the specialization leaves the parameter out, which is the type the
// default specialization binds.
std::string_view TypeActualName(const ClassDecl* decl, size_t i,
                                const DataType* actual) {
  if (actual != nullptr && !actual->type_name.empty()) return actual->type_name;
  if (i < decl->param_types.size()) return decl->param_types[i].type_name;
  return {};
}

}  // namespace

ClassTypeInfo* SpecializationOf(ClassTypeInfo* generic,
                                const std::vector<DataType>& actuals,
                                SimContext& ctx, Arena& arena) {
  if (generic == nullptr || generic->decl == nullptr || actuals.empty())
    return generic;
  const ClassDecl* decl = generic->decl;
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
    const DataType* actual = ActualForParam(actuals, i, pname);
    if (decl->type_param_names.count(pname) != 0) {
      key += TypeActualName(decl, i, actual);
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
  // The declaration's type is copied rather than built again: the base, the
  // interfaces, the members, the vtable and the methods are facts about the
  // declaration and are shared by every specialization, and only the static
  // storage and the parameters standing in it are the specialization's own.
  auto* spec = arena.Create<ClassTypeInfo>(*generic);
  spec->name = *arena.Create<std::string>(std::move(key));
  for (auto& [pname, value] : values)
    spec->static_properties[std::string(pname)] = value;
  ctx.RegisterClassType(spec->name, spec);
  InitSpecializationStaticProperties(spec, ctx, arena);
  return spec;
}

}  // namespace delta
