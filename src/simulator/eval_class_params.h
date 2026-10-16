#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

class Arena;
struct ClassDecl;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
class SimContext;
struct Variable;

// §6.20.2 (printed pages 126-127) with §7.4.4 (printed 155): the width a
// parameter declared with `type` is read at in the simulator.
// DeclaredParamTypeWidth answers wherever it can. A typedef name it leaves
// unsized -- no TypedefRegistryGuard holding the design's typedefs is live
// while the simulator runs -- is read from the design's type table
// (SimContext::FindTypeWidth) under its "Scope::name" or bare key, times the
// packed dimensions written on the name, where the name stands for an
// integral type. 0 where neither answers, and for a real, which is kept a
// real rather than cut to its bits.
uint32_t SimParamTypeWidth(const DataType& type, const ScopeMap& scope,
                           const SimContext& ctx);

// §6.20.2 with §7.4.1 (printed page 153): whether that parameter is signed. A
// typedef name written bare has the sign the design's type table records for
// it; any other type, a typedef name with packed dimensions written on it
// among them, has the sign written with it.
bool SimParamTypeIsSigned(const DataType& type, const SimContext& ctx);

// §8.25 (printed page 203) with §6.20.2 (printed 126-127) and §11.6.1: a
// class's value parameters, each sized by the type its declaration writes.
// A default or a specialization's actual is the right-hand side of an
// assignment to the parameter, so it is evaluated at the declared width --
// an unbased unsized literal filling `logic [W-1:0]` (§5.7.1), a wider actual
// cut to it -- and §8.25.1 lets the range name an earlier parameter, so the
// parameters are taken in header order and each one's value is recorded for
// the ranges after it. A typedef name is sized by SimParamTypeWidth. A type
// that fixes no width, one whose bounds do not fold and a real leave the
// value self-determined, as every parameter was before.
class ClassParamSizer {
 public:
  explicit ClassParamSizer(const ClassDecl* decl) : decl_(decl) {}

  // `type_scope` is the path the class's typedefs are keyed under,
  // "Outer::Inner" for a class nested in another (§8.23); the class's own
  // name where none is given.
  ClassParamSizer(const ClassDecl* decl, std::string_view type_scope)
      : decl_(decl), type_scope_(type_scope) {}

  // The class whose parameters this sizes.
  const ClassDecl* decl() const { return decl_; }

  // The value of the class's i-th parameter from `expr`, and recorded.
  Logic4Vec Value(size_t i, const Expr* expr, SimContext& ctx, Arena& arena);

  // The value of a parameter declared with `type` -- a body parameter's, which
  // the header's list does not index -- from `expr`, recorded under `name`.
  Logic4Vec Value(std::string_view name, const DataType* type, const Expr* expr,
                  SimContext& ctx, Arena& arena);

  // Records the i-th parameter's value that stands already, for the ranges
  // after it: an object's default kept beside a specialization's overrides.
  void Record(size_t i, const Logic4Vec& val);

 private:
  const ClassDecl* decl_;
  std::string_view type_scope_;
  ScopeMap scope_;
};

// §8.25 (printed page 203) with §8.25.1: a specialization's parameters are
// bound throughout the class body, so a method the body enters -- a bare call
// to another static method of the class, the constructor `C#(7)::new` runs
// and the property defaults it reads -- sees what the call that named the
// specialization bound: the value parameters BindClassParams (eval_function.
// cpp) made locals of the naming call's frame, under the bare name and the
// `Class.param` spelling, and the type actuals BindClassScopeTypeActuals
// (eval_class_scope_types.cpp) bound in it. The bindings are collected from
// the frames the entering call sees, before its own frame is pushed, and
// bound again in that frame once it is: §23.9 ends a body's search for a
// bare name at the body's own frame (ScopeStack::VisibleFramesEnd), so a
// binding left in the caller's frame is out of the callee's reach, where
// the walk through every frame once reached it.
struct ClassParamBinding {
  std::string_view name;
  Variable* value = nullptr;
  const DataType* type = nullptr;
};
// §6.20.7 (printed page 131): marks in obj->unbounded_params each value
// parameter `decl` declares, in its header or its body, whose default is `$`
// or names another parameter of the class already marked, for §20.6.3's
// $isunbounded.
void MarkUnboundedClassParams(ClassObject* obj, const ClassDecl* decl);

std::vector<ClassParamBinding> CollectClassParamBindings(
    const ClassTypeInfo* cls, SimContext& ctx);
void RebindClassParamBindings(const std::vector<ClassParamBinding>& bindings,
                              SimContext& ctx);

// Answers the value a header parameter of a class holds, or null where it
// holds none; and stores a body parameter's folded value.
using ParamValueLookup = std::function<const Logic4Vec*(std::string_view)>;
using ParamValueStore = std::function<void(std::string_view, const Logic4Vec&)>;

// §6.20.4 with §8.25: a parameter declared in a class's body, `localparam int
// N = W * 2`, is a constant of each specialization, folded over that
// specialization's header parameters. Each value parameter of the header of
// the class `sizer` sizes that `header` answers is bound in a scope of its
// own, and each body parameter with an initializer is folded there by
// `sizer`, in declaration order, and handed to `store`; the sizer carries the
// path the class's typedefs are keyed under. Folded with no header parameter
// bound, as the class was lowered, the name read nothing and every
// specialization's N was 0.
void FoldClassBodyParams(ClassParamSizer sizer, const ParamValueLookup& header,
                         const ParamValueStore& store, SimContext& ctx,
                         Arena& arena);

// The lookup and store FoldClassBodyParams takes for a class's own copy of
// its parameters, the static storage of the class or a specialization.
ParamValueLookup ClassStaticLookup(const ClassTypeInfo* info);
ParamValueStore ClassStaticStore(ClassTypeInfo* info);

// §8.25 with §20.6.2: the type each type parameter of `decl` stands for
// under the actuals `actuals` -- the one an actual gives it, else the default
// the class declares -- keyed by the parameter's name, with the typedef such a
// type names in turn under its own name, so a TypedefRegistryGuard holding
// the table folds `bit [$bits(T)-1:0]` as wide as T. A parameter given
// neither an actual nor a default is left out.
TypedefMap TypeParamTypes(const ClassDecl* decl,
                          const std::vector<DataType>& actuals,
                          const SimContext& ctx);

}  // namespace delta
